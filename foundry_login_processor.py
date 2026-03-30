"""
Foundry Login Processor
------------------------
Runs automatically when Emily logs in (via Windows Startup folder shortcut).
Scans Dropbox for source videos missing SRT / Words JSON / Captioned output
and processes them immediately.

Key behavior:
  - Waits 60 seconds on login for Dropbox to sync
  - Checks .last_run_date to avoid double-running on same day
  - Walks Dropbox (excluding skip list) for missing assets
  - Processes EACH source video independently
  - Uses exact canonical output paths per source video
  - NEVER auto-processes 3MB videos
  - NEVER auto-processes Unstuck/Theological Reflections videos
  - NEVER processes audio-only folders listed in AUDIO_ONLY_SKIP_FOLDERS
  - Adapts caption size AND words-per-frame for portrait videos
  - Lets you stop after the current item from the UI
  - Always shows a status window, even when nothing needs processing
"""

import os
import re
import sys
import json
import time
import shutil
import tempfile
import textwrap
import datetime
import threading
import subprocess
import ctypes
import tkinter as tk
import tkinter.ttk as ttk
import tkinter.messagebox as mb

# ── Prevent Windows sleep ─────────────────────────────────────────────────────
ES_CONTINUOUS       = 0x80000000
ES_SYSTEM_REQUIRED  = 0x00000001
ES_DISPLAY_REQUIRED = 0x00000002
ctypes.windll.kernel32.SetThreadExecutionState(
    ES_CONTINUOUS | ES_SYSTEM_REQUIRED | ES_DISPLAY_REQUIRED
)

# ── Config ────────────────────────────────────────────────────────────────────
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
DROPBOX_ROOT = os.path.join(os.path.expanduser("~"), "Dropbox")
MB3_PATH = os.path.join(DROPBOX_ROOT, "3MB")
RAN_TODAY_MARKER = os.path.join(SCRIPT_DIR, ".last_run_date")
LOG_PATH = os.path.join(SCRIPT_DIR, "foundry_login_processor_log.txt")

WHISPER_MODEL = "medium"
STYLE_STR = "Fontname=Arial,Outline=1,Shadow=0,BorderStyle=1,Spacing=1"
DROPBOX_SYNC_WAIT = 60
CREATE_NO_WINDOW = 0x08000000 if sys.platform == "win32" else 0

SOURCE_VIDEO_EXTS = {".mp4", ".mov"}
VIDEO_EXTS = {".mp4", ".mov"}

SKIP_FOLDERS = {
    "3mb",
    "scripts",
    "ffmpeg",
    "on-demand lessons",
    "operations",
    "youtube",
    "social media clips",
    ".dropbox.cache",
    "dropbox cache",
}

AUDIO_ONLY_SKIP_FOLDERS = {
    os.path.normcase(os.path.join(DROPBOX_ROOT, "Podcast", "Wholehearted Ministry")),
}

THEO_REFLECTIONS_PATH = os.path.normcase(
    os.path.join(DROPBOX_ROOT, "Unstuck", "Theological Reflections")
)

CF_ORANGE  = "#E8541A"
CF_BG      = "#111111"
CF_SURFACE = "#1C1C1C"
CF_BORDER  = "#333333"
CF_WHITE   = "#FFFFFF"
CF_GRAY    = "#888888"
CF_GREEN   = "#2D6A4F"
CF_AMBER   = "#F5A623"
CF_RED     = "#E05555"


# ══════════════════════════════════════════════════════════════════════════════
# SOURCE / OUTPUT DETECTION
# ══════════════════════════════════════════════════════════════════════════════

def normalize_spaces(s: str) -> str:
    return re.sub(r"\s+", " ", s).strip()


def tokenize_stem(filename: str) -> list[str]:
    stem = os.path.splitext(filename)[0].lower()
    tokens = re.split(r"[\s\-_()\[\]{}.,]+", stem)
    return [t for t in tokens if t]


def get_base_name(filepath: str) -> str:
    name = os.path.splitext(os.path.basename(filepath))[0]
    name = re.sub(r"\s*\((?:uncaptioned|uncap|raw|source)\)\s*$", "", name, flags=re.IGNORECASE)
    name = re.sub(r"\s*[-–_]\s*(?:uncaptioned|uncap|raw|source)\s*$", "", name, flags=re.IGNORECASE)
    return normalize_spaces(name)


def canonical_output_paths(source_path: str) -> dict:
    folder = os.path.dirname(source_path)
    base = get_base_name(source_path)
    return {
        "base_name": base,
        "srt": os.path.join(folder, f"{base} - Transcript (Time-Stamped).srt"),
        "words": os.path.join(folder, f"{base} - Transcript (Words).json"),
        "captioned": os.path.join(folder, f"{base} (Captioned).mp4"),
    }


def looks_like_captioned_video(filename: str) -> bool:
    stem = os.path.splitext(filename)[0].lower()

    if re.search(r'(^|[\s\-_()\[\]{}.,])uncaptioned($|[\s\-_()\[\]{}.,])', stem):
        return False
    if re.search(r'(^|[\s\-_()\[\]{}.,])uncap($|[\s\-_()\[\]{}.,])', stem):
        return False
    if re.search(r'(^|[\s\-_()\[\]{}.,])raw($|[\s\-_()\[\]{}.,])', stem):
        return False
    if re.search(r'(^|[\s\-_()\[\]{}.,])source($|[\s\-_()\[\]{}.,])', stem):
        return False

    return re.search(r'(^|[\s\-_()\[\]{}.,])captioned($|[\s\-_()\[\]{}.,])', stem) is not None


def is_derivative_filename(filename: str) -> bool:
    lower = filename.lower()
    ext = os.path.splitext(lower)[1]

    if ext == ".srt":
        return True

    if ext == ".json":
        return True

    tokens = set(tokenize_stem(filename))

    if "transcript" in tokens:
        return True
    if "subtitles" in tokens or "subtitle" in tokens or "subtitled" in tokens:
        return True
    if "timestamped" in tokens:
        return True
    if "words" in tokens and ext in {".json", ".txt", ".docx", ".doc"}:
        return True

    if ext in VIDEO_EXTS and looks_like_captioned_video(filename):
        return True

    return False


def iter_source_files(files: list[str], folder: str) -> list[str]:
    candidates = []
    for f in files:
        ext = os.path.splitext(f)[1].lower()
        if ext not in SOURCE_VIDEO_EXTS:
            continue
        if is_derivative_filename(f):
            continue
        candidates.append(os.path.join(folder, f))

    candidates.sort(key=lambda p: os.path.basename(p).lower())
    return candidates


def is_theological_reflections_folder(folder: str) -> bool:
    folder_norm = os.path.normcase(os.path.abspath(folder))
    return folder_norm == THEO_REFLECTIONS_PATH or folder_norm.startswith(THEO_REFLECTIONS_PATH + os.sep)


def is_audio_only_skip_folder(folder: str) -> bool:
    folder_norm = os.path.normcase(os.path.abspath(folder))
    for skip_path in AUDIO_ONLY_SKIP_FOLDERS:
        if folder_norm == skip_path or folder_norm.startswith(skip_path + os.sep):
            return True
    return False


def _should_skip_dir(dirpath: str) -> bool:
    try:
        rel = os.path.relpath(dirpath, DROPBOX_ROOT)
    except ValueError:
        return True
    top = rel.split(os.sep)[0].lower()
    return top in SKIP_FOLDERS


# ══════════════════════════════════════════════════════════════════════════════
# ADAPTIVE CAPTION STYLING
# ══════════════════════════════════════════════════════════════════════════════

def get_video_dimensions(video_path: str, ffmpeg_exe: str) -> tuple[int, int]:
    def _probe(ffprobe_exe: str) -> tuple[int, int]:
        result = subprocess.run(
            [ffprobe_exe, "-v", "error", "-select_streams", "v:0",
             "-show_entries", "stream=width,height", "-of", "json", video_path],
            capture_output=True, text=True, timeout=10,
            creationflags=CREATE_NO_WINDOW,
        )
        data = json.loads(result.stdout)
        return data["streams"][0]["width"], data["streams"][0]["height"]

    ffprobe = ffmpeg_exe.replace("ffmpeg.exe", "ffprobe.exe") if ffmpeg_exe != "ffmpeg" else "ffprobe"
    try:
        return _probe(ffprobe)
    except Exception:
        if ffprobe != "ffprobe":
            try:
                return _probe("ffprobe")
            except Exception:
                pass
        return 1920, 1080


def get_caption_style(width: int, height: int) -> dict:
    aspect = width / height if height > 0 else 1.78

    if aspect < 0.75:
        return {
            "fontsize": 20,
            "margin_v": int(height * 0.15),
            "margin_h": int(width * 0.07),
            "label": "vertical",
            "max_words": 3,
            "max_line_len": 16,
        }
    elif aspect > 1.4:
        return {
            "fontsize": 22,
            "margin_v": int(height * 0.06),
            "margin_h": int(width * 0.04),
            "label": "horizontal",
            "max_words": 10,
            "max_line_len": 35,
        }
    else:
        return {
            "fontsize": 22,
            "margin_v": int(height * 0.08),
            "margin_h": int(width * 0.05),
            "label": "square",
            "max_words": 6,
            "max_line_len": 24,
        }


# ══════════════════════════════════════════════════════════════════════════════
# SCANNING
# ══════════════════════════════════════════════════════════════════════════════

def scan_dropbox() -> list[dict]:
    work_items = []

    if not os.path.isdir(DROPBOX_ROOT):
        return work_items

    for root, dirs, files in os.walk(DROPBOX_ROOT):
        if root == DROPBOX_ROOT:
            dirs[:] = [d for d in dirs if d.lower() not in SKIP_FOLDERS]
            continue

        if _should_skip_dir(root):
            dirs[:] = []
            continue

        if is_audio_only_skip_folder(root):
            dirs[:] = []
            continue

        if is_theological_reflections_folder(root):
            dirs[:] = []
            continue

        sources = iter_source_files(files, root)
        if not sources:
            continue

        for source in sources:
            outputs = canonical_output_paths(source)
            got_srt = os.path.exists(outputs["srt"])
            got_words = os.path.exists(outputs["words"])
            got_cap = os.path.exists(outputs["captioned"])

            needs_srt = not got_srt
            needs_words = not got_words
            needs_cap = not got_cap

            if needs_srt or needs_words or needs_cap:
                try:
                    display_path = os.path.relpath(root, DROPBOX_ROOT)
                except ValueError:
                    display_path = root

                work_items.append({
                    "source": source,
                    "base_name": outputs["base_name"],
                    "folder": root,
                    "display_path": display_path,
                    "needs_srt": needs_srt,
                    "needs_words": needs_words,
                    "needs_cap": needs_cap,
                    "srt_path": outputs["srt"],
                    "words_path": outputs["words"],
                    "cap_path": outputs["captioned"],
                })

    return work_items


def scan_3mb() -> list[str]:
    return []


# ══════════════════════════════════════════════════════════════════════════════
# RAN-TODAY GUARD
# ══════════════════════════════════════════════════════════════════════════════

def already_ran_today() -> bool:
    today = datetime.date.today().isoformat()
    if os.path.exists(RAN_TODAY_MARKER):
        try:
            with open(RAN_TODAY_MARKER, "r", encoding="utf-8") as f:
                return f.read().strip() == today
        except Exception:
            pass
    return False


def mark_ran_today() -> None:
    try:
        with open(RAN_TODAY_MARKER, "w", encoding="utf-8") as f:
            f.write(datetime.date.today().isoformat())
    except Exception:
        pass


# ══════════════════════════════════════════════════════════════════════════════
# LOGGING
# ══════════════════════════════════════════════════════════════════════════════

_log_lines = []
_log_callback = None


def log(msg: str = "") -> None:
    _log_lines.append(msg)
    if _log_callback:
        _log_callback(msg)


def write_log() -> None:
    try:
        with open(LOG_PATH, "a", encoding="utf-8") as f:
            f.write("\n".join(_log_lines) + "\n\n")
    except Exception:
        pass


# ══════════════════════════════════════════════════════════════════════════════
# TRANSCRIPTION + CAPTION BURNING
# ══════════════════════════════════════════════════════════════════════════════

def srt_time(s: float) -> str:
    ms = int((s % 1) * 1000)
    return f"{int(s)//3600:02d}:{(int(s)//60)%60:02d}:{int(s)%60:02d},{ms:03d}"


def make_srt(segments: list[dict], max_words: int = 10, max_line_len: int = 35) -> str:
    all_words = []
    for seg in segments:
        if "words" in seg and seg["words"]:
            for w in seg["words"]:
                word = w.get("word", "").strip()
                start = w.get("start", seg["start"])
                end = w.get("end", seg["end"])
                if word:
                    all_words.append({"word": word, "start": start, "end": end})
        else:
            all_words.append({
                "word": seg["text"].strip(),
                "start": seg["start"],
                "end": seg["end"],
                "_is_segment": True,
            })

    if not all_words:
        return ""

    chunks = []
    i = 0
    while i < len(all_words):
        chunk = all_words[i:i + max_words]
        if chunk[0].get("_is_segment"):
            chunks.append(chunk)
            i += 1
        else:
            chunks.append(chunk)
            i += max_words

    lines = []
    for idx, chunk in enumerate(chunks, 1):
        start = chunk[0]["start"]
        end = chunk[-1]["end"]

        if chunk[0].get("_is_segment"):
            text = chunk[0]["word"]
        else:
            text = " ".join(w["word"] for w in chunk)

        wrapped = "\n".join(textwrap.wrap(text, max_line_len))
        lines += [str(idx), f"{srt_time(start)} --> {srt_time(end)}", wrapped, ""]

    return "\n".join(lines)


def make_words_json(segments: list[dict]) -> str:
    words = []
    for seg in segments:
        if "words" in seg:
            for w in seg["words"]:
                words.append({
                    "word": w.get("word", "").strip(),
                    "start": round(w.get("start", seg["start"]), 3),
                    "end": round(w.get("end", seg["end"]), 3),
                })
        else:
            for word in seg["text"].split():
                words.append({
                    "word": word.strip(),
                    "start": round(seg["start"], 3),
                    "end": round(seg["end"], 3),
                })
    return json.dumps(words, indent=2, ensure_ascii=False)


def ensure_local(path: str, timeout: int = 600, poll_interval: int = 10) -> bool:
    if not os.path.exists(path):
        log(f"  File not found: {path}")
        return False

    try:
        with open(path, "rb") as f:
            f.read(1024)
        return True
    except Exception:
        pass

    log(f"  File not yet local, waiting for Dropbox sync (up to {timeout//60} min)...")
    start = time.time()

    while time.time() - start < timeout:
        try:
            with open(path, "rb") as f:
                data = f.read(1024)
            if data:
                log("  ✓ File is now local.")
                time.sleep(5)
                return True
        except Exception:
            pass
        time.sleep(poll_interval)

    log(f"  ✗ Timed out waiting for Dropbox to download {os.path.basename(path)}")
    return False


def burn_captions(video_in: str, srt_path: str, video_out: str) -> bool:
    tmp_dir = tempfile.gettempdir()
    temp_out = os.path.join(tmp_dir, "foundry_burn_temp.mp4")
    tmp_srt = os.path.join(tmp_dir, "foundry_caption_temp.srt")
    tmp_video = os.path.join(tmp_dir, "foundry_src_burn_temp.mp4")

    width, height = get_video_dimensions(video_in, "ffmpeg")
    cap_style = get_caption_style(width, height)

    dynamic_style = (
        f"Fontsize={cap_style['fontsize']},"
        f"{STYLE_STR},"
        f"MarginV={cap_style['margin_v']},"
        f"MarginH={cap_style['margin_h']}"
    )

    shutil.copy2(video_in, tmp_video)
    shutil.copy2(srt_path, tmp_srt)
    srt_escaped = tmp_srt.replace("\\", "/").replace(":", "\\:")
    video_in = tmp_video

    result = subprocess.run([
        "ffmpeg", "-y",
        "-i", video_in,
        "-vf", f"subtitles='{srt_escaped}':force_style='{dynamic_style}'",
        "-c:v", "libx264", "-preset", "ultrafast", "-crf", "23",
        "-c:a", "copy",
        temp_out
    ], capture_output=True, text=True, creationflags=CREATE_NO_WINDOW)

    if result.returncode == 0 and os.path.exists(temp_out):
        shutil.copy2(temp_out, video_out)
        for p in [temp_out, tmp_srt, tmp_video]:
            if os.path.exists(p):
                try:
                    os.remove(p)
                except Exception:
                    pass
        return True

    log(f"    ffmpeg error: {result.stderr[-400:]}")
    for p in [temp_out, tmp_srt, tmp_video]:
        if os.path.exists(p):
            try:
                os.remove(p)
            except Exception:
                pass
    return False


def process_item(item: dict, model) -> bool:
    source = item["source"]
    srt_path = item["srt_path"]
    words_path = item["words_path"]
    cap_path = item["cap_path"]

    audio_temp = os.path.join(tempfile.gettempdir(), "foundry_audio_temp.wav")
    clean_source = None
    success = True

    try:
        if item["needs_srt"] or item["needs_words"]:
            log("  Ensuring file is downloaded from Dropbox...")
            if not ensure_local(source):
                log("  ✗ Could not download file from Dropbox — skipping.")
                return False

            src_ext = os.path.splitext(source)[1].lower()
            clean_source = os.path.join(tempfile.gettempdir(), f"foundry_src_temp{src_ext}")
            shutil.copy2(source, clean_source)

            log("  Extracting audio...")
            try:
                subprocess.run([
                    "ffmpeg", "-y", "-i", clean_source,
                    "-vn", "-acodec", "pcm_s16le", "-ar", "16000", "-ac", "1",
                    audio_temp
                ], check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                   creationflags=CREATE_NO_WINDOW)
            finally:
                if clean_source and os.path.exists(clean_source):
                    try:
                        os.remove(clean_source)
                        clean_source = None
                    except Exception:
                        pass

            log(f"  Transcribing with Whisper {WHISPER_MODEL}...")
            result = model.transcribe(audio_temp, language="en", word_timestamps=True)
            segments = result["segments"]
            if os.path.exists(audio_temp):
                os.remove(audio_temp)

            width, height = get_video_dimensions(source, "ffmpeg")
            caption_style = get_caption_style(width, height)

            if item["needs_srt"]:
                with open(srt_path, "w", encoding="utf-8") as f:
                    f.write(make_srt(
                        segments,
                        max_words=caption_style["max_words"],
                        max_line_len=caption_style["max_line_len"],
                    ))
                log(f"  ✓ SRT saved ({caption_style['label']} chunking).")

            if item["needs_words"]:
                with open(words_path, "w", encoding="utf-8") as f:
                    f.write(make_words_json(segments))
                log("  ✓ Words JSON saved.")

        if item["needs_cap"]:
            if not os.path.exists(srt_path):
                log("  ✗ No SRT found — cannot burn captions. Skipping burn.")
                return False

            log("  Ensuring file is downloaded from Dropbox...")
            if not ensure_local(source):
                log("  ✗ Could not download file from Dropbox — skipping burn.")
                return False

            log("  Burning captions...")
            ok = burn_captions(source, srt_path, cap_path)
            if ok:
                log("  ✓ Captioned video saved.")
            else:
                log("  ✗ Caption burn failed.")
                success = False

    except Exception as e:
        log(f"  ✗ ERROR: {e}")
        success = False
    finally:
        if clean_source and os.path.exists(clean_source):
            try:
                os.remove(clean_source)
            except Exception:
                pass
        if os.path.exists(audio_temp):
            try:
                os.remove(audio_temp)
            except Exception:
                pass

    return success


# ══════════════════════════════════════════════════════════════════════════════
# STATUS WINDOW
# ══════════════════════════════════════════════════════════════════════════════

class StatusWindow:
    def __init__(self, work_items, new_3mb):
        self.work_items = work_items
        self.new_3mb = new_3mb
        self.root = None
        self.log_text = None
        self.status_label = None
        self.progress_bar = None
        self.done_btn = None
        self.stop_after_current = False

    def _append_log(self, msg):
        if self.log_text and self.root:
            self.root.after(0, self._do_append, msg)

    def _do_append(self, msg):
        self.log_text.config(state="normal")
        self.log_text.insert("end", msg + "\n")
        self.log_text.see("end")
        self.log_text.config(state="disabled")

    def _set_status(self, msg, color=CF_GRAY):
        if self.status_label and self.root:
            self.root.after(0, lambda: self.status_label.config(text=msg, fg=color))

    def _set_progress(self, value):
        if self.progress_bar and self.root:
            self.root.after(0, lambda: self.progress_bar.config(value=value))

    def _request_stop(self):
        self.stop_after_current = True
        self._set_status("Will stop after current item...", CF_AMBER)
        log("Stop requested — will stop after current item.")

    def _build_ui(self):
        root = tk.Tk()
        root.title("Foundry — Processing Videos")
        root.configure(bg=CF_BG)
        root.resizable(True, True)
        root.minsize(560, 420)

        w, h = 640, 540
        x = (root.winfo_screenwidth() - w) // 2
        y = (root.winfo_screenheight() - h) // 2
        root.geometry(f"{w}x{h}+{x}+{y}")

        tk.Frame(root, bg=CF_ORANGE, height=5).pack(fill="x")

        title_row = tk.Frame(root, bg=CF_BG)
        title_row.pack(fill="x", padx=20, pady=(14, 2))
        tk.Label(title_row, text="Foundry Video Processor",
                 font=("Segoe UI", 13, "bold"),
                 bg=CF_BG, fg=CF_WHITE).pack(side="left")
        tk.Label(title_row, text=f"{len(self.work_items)} video(s) queued",
                 font=("Segoe UI", 9), bg=CF_BG, fg=CF_GRAY).pack(side="right", pady=2)

        if self.new_3mb:
            alert = tk.Frame(root, bg="#3A1A00")
            alert.pack(fill="x", padx=20, pady=(4, 0))
            tk.Label(
                alert,
                text=f"  ⚠  {len(self.new_3mb)} new 3MB file(s) detected — use Caption App (manual workflow)",
                font=("Segoe UI", 9), anchor="w",
                bg="#3A1A00", fg=CF_AMBER
            ).pack(fill="x", pady=5, padx=8)

        self.status_label = tk.Label(root, text="Waiting...",
                                     font=("Segoe UI", 9),
                                     bg=CF_BG, fg=CF_GRAY, anchor="w")
        self.status_label.pack(fill="x", padx=20, pady=(8, 2))

        style = ttk.Style()
        style.theme_use("default")
        style.configure("F.Horizontal.TProgressbar",
                        troughcolor=CF_SURFACE,
                        background=CF_ORANGE,
                        bordercolor=CF_BORDER,
                        lightcolor=CF_ORANGE,
                        darkcolor=CF_ORANGE)
        self.progress_bar = ttk.Progressbar(
            root,
            style="F.Horizontal.TProgressbar",
            orient="horizontal",
            mode="determinate",
            maximum=max(len(self.work_items), 1)
        )
        self.progress_bar.pack(fill="x", padx=20, pady=(0, 8))

        log_outer = tk.Frame(root, bg=CF_SURFACE,
                             highlightthickness=1, highlightbackground=CF_BORDER)
        log_outer.pack(fill="both", expand=True, padx=20, pady=(0, 10))

        self.log_text = tk.Text(log_outer,
                                bg=CF_SURFACE, fg="#C8C8C8",
                                font=("Consolas", 8),
                                state="disabled", wrap="word",
                                relief="flat", bd=0,
                                padx=8, pady=6,
                                insertbackground=CF_WHITE)
        scrollbar = tk.Scrollbar(log_outer, orient="vertical",
                                 command=self.log_text.yview,
                                 bg=CF_SURFACE, troughcolor=CF_BG)
        self.log_text.configure(yscrollcommand=scrollbar.set)
        scrollbar.pack(side="right", fill="y")
        self.log_text.pack(side="left", fill="both", expand=True)

        btn_row = tk.Frame(root, bg=CF_BG)
        btn_row.pack(fill="x", padx=20, pady=(0, 14))

        tk.Button(
            btn_row,
            text="Stop After Current",
            font=("Segoe UI", 9),
            bg=CF_SURFACE, fg=CF_GRAY,
            activebackground="#2a2a2a", activeforeground=CF_WHITE,
            relief="flat", padx=20, pady=5,
            command=self._request_stop
        ).pack(side="left")

        self.done_btn = tk.Button(btn_row, text="Done",
                                  font=("Segoe UI", 9, "bold"),
                                  bg=CF_SURFACE, fg=CF_GRAY,
                                  activebackground="#2a2a2a",
                                  activeforeground=CF_WHITE,
                                  relief="flat", padx=20, pady=5,
                                  state="disabled",
                                  command=root.destroy)
        self.done_btn.pack(side="right")

        tk.Button(btn_row, text="Minimize",
                  font=("Segoe UI", 9),
                  bg=CF_SURFACE, fg=CF_GRAY,
                  activebackground="#2a2a2a", activeforeground=CF_WHITE,
                  relief="flat", padx=20, pady=5,
                  command=root.iconify).pack(side="right", padx=(0, 8))

        self.root = root

    def _processing_thread(self):
        global _log_callback
        _log_callback = self._append_log

        log(f"Started: {datetime.datetime.now().strftime('%Y-%m-%d %H:%M')}")
        log()

        self._set_status("Loading Whisper model...", CF_AMBER)
        log("Loading Whisper model (this may take a moment)...")

        try:
            import whisper
            model = whisper.load_model(WHISPER_MODEL)
            log(f"✓ Whisper {WHISPER_MODEL} loaded.\n")
        except ImportError:
            log("ERROR: Whisper not installed. Run: pip install openai-whisper")
            self._set_status("Error: Whisper not installed.", CF_RED)
            write_log()
            self.root.after(0, lambda: self.done_btn.config(
                state="normal",
                bg=CF_ORANGE, fg=CF_WHITE,
                activebackground="#c44415",
                activeforeground=CF_WHITE,
            ))
            return

        if not self.work_items and not self.new_3mb:
            log("No videos need processing.")
            self._set_status("No videos need processing.", CF_GREEN)
            write_log()
            ctypes.windll.kernel32.SetThreadExecutionState(ES_CONTINUOUS)
            self.root.after(0, lambda: self.done_btn.config(
                state="normal",
                bg=CF_ORANGE, fg=CF_WHITE,
                activebackground="#c44415",
                activeforeground=CF_WHITE,
            ))
            return

        done = 0
        errors = []

        for i, item in enumerate(self.work_items, 1):
            fname = os.path.basename(item["source"])
            label = f"[{i}/{len(self.work_items)}] {item['display_path']} — {item['base_name']}"
            log(label)
            self._set_status(label, CF_AMBER)

            missing = []
            if item["needs_srt"]:
                missing.append("SRT")
            if item["needs_words"]:
                missing.append("Words JSON")
            if item["needs_cap"]:
                missing.append("Captioned MP4")

            log(f"  Missing: {', '.join(missing) if missing else 'Nothing'}")

            ok = process_item(item, model)
            if ok:
                done += 1
            else:
                errors.append(fname)

            self._set_progress(i)
            log()

            if self.stop_after_current:
                log("Stopped by user after current item.")
                break

        log("═" * 48)
        log(f"✓ Processed : {done}")
        log(f"  Errors    : {len(errors)}")
        for e in errors:
            log(f"    • {e}")

        if errors:
            self._set_status(
                f"Done — {done} processed, {len(errors)} error(s). Check log.", CF_RED)
        else:
            self._set_status(
                f"Done — {done} video(s) processed successfully.", CF_GREEN)

        write_log()

        ctypes.windll.kernel32.SetThreadExecutionState(ES_CONTINUOUS)

        self.root.after(0, lambda: self.done_btn.config(
            state="normal",
            bg=CF_ORANGE, fg=CF_WHITE,
            activebackground="#c44415",
            activeforeground=CF_WHITE,
        ))

    def run(self):
        self._build_ui()
        t = threading.Thread(target=self._processing_thread, daemon=False)
        t.start()
        self.root.mainloop()


# ══════════════════════════════════════════════════════════════════════════════
# ENTRY POINT
# ══════════════════════════════════════════════════════════════════════════════

def main():
    run_now = "--now" in sys.argv

    if not run_now and already_ran_today():
        return

    if run_now:
        print("--now flag detected, skipping sync wait...")
    else:
        print(f"Waiting {DROPBOX_SYNC_WAIT}s for Dropbox to sync...")
        time.sleep(DROPBOX_SYNC_WAIT)

    print("Scanning Dropbox for videos missing transcripts or captions...")
    work_items = scan_dropbox()
    new_3mb = scan_3mb()

    # Always show the UI so you can see what happened
    StatusWindow(work_items, new_3mb).run()

    if not run_now:
        mark_ran_today()

    ctypes.windll.kernel32.SetThreadExecutionState(ES_CONTINUOUS)


if __name__ == "__main__":
    try:
        main()
    except Exception as e:
        import traceback
        err_path = os.path.join(SCRIPT_DIR, "foundry_launcher_error.txt")
        try:
            with open(err_path, "w", encoding="utf-8") as f:
                f.write(traceback.format_exc())
        except Exception:
            pass
        try:
            r = tk.Tk()
            r.withdraw()
            mb.showerror(
                "Foundry Processor Error",
                f"An error occurred:\n\n{e}\n\nSee foundry_launcher_error.txt in Dropbox/Scripts."
            )
            r.destroy()
        except Exception:
            pass
