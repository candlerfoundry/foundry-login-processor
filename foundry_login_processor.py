"""
Foundry Login Processor
------------------------
Replaces foundry_startup_launcher.py + nightly_watcher.py

Runs automatically when Emily logs in (via Windows Startup folder shortcut).
Scans the ENTIRE Dropbox for videos missing SRT / Words JSON / Captioned output
and processes them immediately — no scheduling, no Task Scheduler required.

3MB videos are NEVER processed automatically. A notification appears in the
status window if new 3MB files are detected.

Behavior:
  - Waits 60 seconds on login for Dropbox to sync
  - Checks .last_run_date to avoid double-running on same day
  - Walks ALL of Dropbox (excluding skip list) for missing assets
  - If nothing to do: exits silently, marks today as done
  - If work found: opens a small status window and starts processing immediately
  - All output logged to foundry_login_processor_log.txt (next to this script)

File detection is intentionally flexible:
  Captioned:   (Captioned).mp4  OR  - Captioned.mp4  OR  _Captioned.mp4
  Uncaptioned: (Uncaptioned).mp4  OR  - Uncaptioned.mp4  OR  .mp3  OR  .mov
  Words JSON:  any .json with "word" or "timestamp" in name

Canonical output naming (matches Caption_App.pyw):
  Captioned:   {base} (Captioned).mp4
  SRT:         {base} - Transcript (Time-Stamped).srt
  Words JSON:  {base} - Transcript (Words).json

Audio-only detection: if the source file is an .mp3, captions are skipped.
No hardcoded series list required.

Install:
  1. Press Win+R -> shell:startup -> Enter
  2. Create shortcut with target:
       C:\\Python314\\python.exe C:\\Users\\esavant\\Dropbox\\Scripts\\foundry_login_processor.py
  3. Done — runs every time you log in

Run manually any time (skip sync wait and ran-today guard):
  C:\\Python314\\python.exe foundry_login_processor.py --now
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
SCRIPT_DIR   = os.path.dirname(os.path.abspath(__file__))
DROPBOX_ROOT = os.path.join(os.path.expanduser("~"), "Dropbox")

# Folders directly under Dropbox root to SKIP entirely.
# These are either manually-processed (3MB), infrastructure (Scripts, FFMPEG),
# or not video libraries (On-Demand Lessons, Operations, YouTube, etc.)
SKIP_FOLDERS = {
    "3mb",
    "scripts",
    "ffmpeg",
    "on-demand lessons",
    "operations",
    "youtube",
    "social media clips",   # output folder — never scan for missing assets
    ".dropbox.cache",
    "dropbox cache",
}

MB3_PATH         = os.path.join(DROPBOX_ROOT, "3MB")
RAN_TODAY_MARKER = os.path.join(SCRIPT_DIR, ".last_run_date")
LOG_PATH         = os.path.join(SCRIPT_DIR, "foundry_login_processor_log.txt")

WHISPER_MODEL    = "medium"
STYLE_STR        = "Fontname=Arial,Outline=1,Shadow=0,BorderStyle=1,Spacing=1"
DROPBOX_SYNC_WAIT = 60  # seconds to wait for Dropbox to sync on login

# ── Brand colors ──────────────────────────────────────────────────────────────
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
# FLEXIBLE FILE DETECTION
# Handles naming variance: parens vs dashes, case, extra spaces, etc.
# ══════════════════════════════════════════════════════════════════════════════

def has_captioned(files):
    """
    True if any file looks like a captioned video output.
    Matches: (Captioned).mp4 / - Captioned.mp4 / _captioned.mp4
    Excludes: anything with 'uncaptioned' in the name.
    """
    for f in files:
        fl = f.lower()
        if not fl.endswith('.mp4'):
            continue
        if 'uncaptioned' in fl:
            continue
        if 'captioned' in fl:
            return True
    return False


def has_srt(files):
    return any(f.lower().endswith('.srt') for f in files)


def has_words_json(files):
    """
    True if any .json file looks like a word-timestamp file.
    Matches: Transcript (Words).json / words.json / word_timestamps.json etc.
    """
    for f in files:
        fl = f.lower()
        if not fl.endswith('.json'):
            continue
        stem = os.path.splitext(fl)[0]
        normalized = re.sub(r'[\s\-_()\[\]]+', '', stem)
        if 'word' in normalized or 'timestamp' in normalized:
            return True
    return False


def find_source_file(files, folder):
    """
    Return the full path of the source media file to process, or None.

    Priority:
      0 — (Uncaptioned).mp4 or - Uncaptioned.mp4  (properly named source)
      1 — .mp3  (audio-only source)
      2 — (Uncaptioned).mov / - Uncaptioned.mov
      3 — any .mp4 that is NOT a captioned output  (fallback for mis-named files)
      4 — any .mov that is NOT a captioned output

    This ensures files uploaded without naming conventions are still detected.
    """
    candidates = []
    for f in files:
        fl  = f.lower()
        ext = os.path.splitext(fl)[1]
        is_captioned_output = 'captioned' in fl and 'uncaptioned' not in fl

        if ext == '.mp4':
            if 'uncaptioned' in fl:
                candidates.append((0, f))
            elif not is_captioned_output:
                candidates.append((3, f))
        elif ext == '.mp3':
            candidates.append((1, f))
        elif ext == '.mov':
            if 'uncaptioned' in fl:
                candidates.append((2, f))
            elif not is_captioned_output:
                candidates.append((4, f))

    if not candidates:
        return None
    candidates.sort()
    return os.path.join(folder, candidates[0][1])


def get_base_name(filepath):
    """
    Strip known suffixes from filename to get the shared base name.
    Handles: (Uncaptioned) / - Uncaptioned / _Uncaptioned and .mp3 sources.
    """
    name = os.path.splitext(os.path.basename(filepath))[0]
    name = re.sub(r'\.mp3$', '', name, flags=re.IGNORECASE)
    name = re.sub(r'\s*\(Uncaptioned\)\s*$', '', name, flags=re.IGNORECASE)
    name = re.sub(r'\s*[-–_]\s*Uncaptioned\s*$', '', name, flags=re.IGNORECASE)
    return name.strip()


# ══════════════════════════════════════════════════════════════════════════════
# DROPBOX-WIDE SCANNER
# No hardcoded folder map — walks all of Dropbox, skips excluded folders.
# ══════════════════════════════════════════════════════════════════════════════

def _should_skip_dir(dirpath):
    """
    True if this directory (or any ancestor below DROPBOX_ROOT) matches SKIP_FOLDERS.
    Checked by comparing the first path component under Dropbox root.
    """
    try:
        rel = os.path.relpath(dirpath, DROPBOX_ROOT)
    except ValueError:
        return True  # different drive on Windows — skip
    top = rel.split(os.sep)[0].lower()
    return top in SKIP_FOLDERS


def scan_dropbox():
    """
    Walk the entire Dropbox, skipping excluded folders.
    Return list of work items, each a dict with:
      source, base_name, folder, display_path,
      audio_only, needs_srt, needs_words, needs_cap
    """
    work_items = []

    if not os.path.isdir(DROPBOX_ROOT):
        return work_items

    for root, dirs, files in os.walk(DROPBOX_ROOT):
        # Prune excluded top-level dirs in-place so os.walk won't descend into them
        if root == DROPBOX_ROOT:
            dirs[:] = [d for d in dirs if d.lower() not in SKIP_FOLDERS]
            continue

        if _should_skip_dir(root):
            dirs[:] = []
            continue

        source = find_source_file(files, root)
        if not source:
            continue

        # Audio-only: determined by file type, not folder name
        audio_only = source.lower().endswith('.mp3')

        got_srt   = has_srt(files)
        got_words = has_words_json(files)
        got_cap   = has_captioned(files)

        needs_srt   = not got_srt
        needs_words = not got_words
        needs_cap   = not audio_only and not got_cap

        if needs_srt or needs_words or needs_cap:
            # Human-readable path for display (relative to Dropbox root)
            try:
                display_path = os.path.relpath(root, DROPBOX_ROOT)
            except ValueError:
                display_path = root

            work_items.append({
                "source":       source,
                "base_name":    get_base_name(source),
                "folder":       root,
                "display_path": display_path,
                "audio_only":   audio_only,
                "needs_srt":    needs_srt,
                "needs_words":  needs_words,
                "needs_cap":    needs_cap,
            })

    return work_items


def scan_3mb():
    """Return list of 3MB filenames that have no SRT yet (alert-only, never processed)."""
    new_files = []
    if not os.path.isdir(MB3_PATH):
        return new_files
    for root, dirs, files in os.walk(MB3_PATH):
        if not has_srt(files):
            for f in files:
                if 'uncaptioned' in f.lower() and f.lower().endswith('.mp4'):
                    new_files.append(f)
    return new_files


# ══════════════════════════════════════════════════════════════════════════════
# RAN-TODAY GUARD
# ══════════════════════════════════════════════════════════════════════════════

def already_ran_today():
    today = datetime.date.today().isoformat()
    if os.path.exists(RAN_TODAY_MARKER):
        try:
            with open(RAN_TODAY_MARKER, 'r') as f:
                return f.read().strip() == today
        except Exception:
            pass
    return False


def mark_ran_today():
    try:
        with open(RAN_TODAY_MARKER, 'w') as f:
            f.write(datetime.date.today().isoformat())
    except Exception:
        pass


# ══════════════════════════════════════════════════════════════════════════════
# LOGGING
# ══════════════════════════════════════════════════════════════════════════════

_log_lines    = []
_log_callback = None  # set by StatusWindow to receive live updates


def log(msg=""):
    _log_lines.append(msg)
    if _log_callback:
        _log_callback(msg)


def write_log():
    try:
        with open(LOG_PATH, 'a', encoding='utf-8') as f:
            f.write('\n'.join(_log_lines) + '\n\n')
    except Exception:
        pass


# ══════════════════════════════════════════════════════════════════════════════
# TRANSCRIPTION + CAPTION BURNING
# ══════════════════════════════════════════════════════════════════════════════

def srt_time(s):
    ms = int((s % 1) * 1000)
    return f"{int(s)//3600:02d}:{(int(s)//60)%60:02d}:{int(s)%60:02d},{ms:03d}"


def make_srt(segments):
    lines = []
    for i, seg in enumerate(segments, 1):
        wrapped = "\n".join(textwrap.wrap(seg["text"].strip(), 42))
        lines += [str(i), f"{srt_time(seg['start'])} --> {srt_time(seg['end'])}", wrapped, ""]
    return "\n".join(lines)


def make_words_json(segments):
    words = []
    for seg in segments:
        if "words" in seg:
            for w in seg["words"]:
                words.append({
                    "word":  w.get("word", "").strip(),
                    "start": round(w.get("start", seg["start"]), 3),
                    "end":   round(w.get("end",   seg["end"]),   3),
                })
        else:
            for word in seg["text"].split():
                words.append({
                    "word":  word.strip(),
                    "start": round(seg["start"], 3),
                    "end":   round(seg["end"],   3),
                })
    return json.dumps(words, indent=2, ensure_ascii=False)


def ensure_local(path, timeout=600, poll_interval=10):
    """Trigger Dropbox to download a cloud-only file. Waits up to timeout seconds."""
    if not os.path.exists(path):
        log(f"  File not found: {path}")
        return False

    try:
        with open(path, 'rb') as f:
            f.read(1024)
        return True  # Already local
    except Exception:
        pass

    log(f"  File not yet local, waiting for Dropbox sync (up to {timeout//60} min)...")

    start = time.time()
    while time.time() - start < timeout:
        try:
            with open(path, 'rb') as f:
                data = f.read(1024)
            if data:
                log(f"  ✓ File is now local.")
                time.sleep(5)
                return True
        except Exception:
            pass
        time.sleep(poll_interval)

    log(f"  ✗ Timed out waiting for Dropbox to download {os.path.basename(path)}")
    return False


def burn_captions(video_in, srt_path, video_out):
    """Burn SRT captions into video. Uses temp paths to handle special chars."""
    tmp_dir   = tempfile.gettempdir()
    temp_out  = os.path.join(tmp_dir, "foundry_burn_temp.mp4")
    tmp_srt   = os.path.join(tmp_dir, "foundry_caption_temp.srt")
    tmp_video = os.path.join(tmp_dir, "foundry_src_burn_temp.mp4")

    shutil.copy2(video_in, tmp_video)
    shutil.copy2(srt_path, tmp_srt)
    srt_escaped = tmp_srt.replace("\\", "/").replace(":", "\\:")
    video_in    = tmp_video

    result = subprocess.run([
        "ffmpeg", "-y",
        "-i", video_in,
        "-vf", f"subtitles='{srt_escaped}':force_style='{STYLE_STR}'",
        "-c:v", "libx264", "-preset", "ultrafast", "-crf", "23",
        "-c:a", "copy",
        temp_out
    ], capture_output=True, text=True,
       creationflags=0x08000000 if sys.platform == "win32" else 0)

    if result.returncode == 0 and os.path.exists(temp_out):
        shutil.copy2(temp_out, video_out)
        for p in [temp_out, tmp_srt, tmp_video]:
            if os.path.exists(p):
                try: os.remove(p)
                except Exception: pass
        return True
    else:
        log(f"    ffmpeg error: {result.stderr[-400:]}")
        for p in [temp_out, tmp_srt, tmp_video]:
            if os.path.exists(p):
                try: os.remove(p)
                except Exception: pass
        return False


def process_item(item, model):
    """Process one video/audio item. Returns True on full success."""
    source    = item["source"]
    base_name = item["base_name"]
    folder    = item["folder"]

    srt_path   = os.path.join(folder, f"{base_name} - Transcript (Time-Stamped).srt")
    words_path = os.path.join(folder, f"{base_name} - Transcript (Words).json")
    cap_path   = os.path.join(folder, f"{base_name} (Captioned).mp4")

    audio_temp  = os.path.join(tempfile.gettempdir(), "foundry_audio_temp.wav")
    clean_source = None
    success     = True

    try:
        # ── Transcription ─────────────────────────────────────────────────
        if item["needs_srt"] or item["needs_words"]:
            log("  Ensuring file is downloaded from Dropbox...")
            if not ensure_local(source):
                log("  ✗ Could not download file from Dropbox — skipping.")
                return False

            src_ext      = os.path.splitext(source)[1].lower()
            clean_source = os.path.join(tempfile.gettempdir(), f"foundry_src_temp{src_ext}")
            shutil.copy2(source, clean_source)

            log("  Extracting audio...")
            try:
                subprocess.run([
                    "ffmpeg", "-y", "-i", clean_source,
                    "-vn", "-acodec", "pcm_s16le", "-ar", "16000", "-ac", "1",
                    audio_temp
                ], check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                   creationflags=0x08000000 if sys.platform == "win32" else 0)
            finally:
                if clean_source and os.path.exists(clean_source):
                    try:
                        os.remove(clean_source)
                        clean_source = None
                    except Exception:
                        pass

            log(f"  Transcribing with Whisper {WHISPER_MODEL}...")
            result   = model.transcribe(audio_temp, language="en", word_timestamps=True)
            segments = result["segments"]
            if os.path.exists(audio_temp):
                os.remove(audio_temp)
            log(f"  ✓ Transcription complete — {len(segments)} segments.")

            if item["needs_srt"]:
                with open(srt_path, "w", encoding="utf-8") as f:
                    f.write(make_srt(segments))
                log("  ✓ SRT saved.")

            if item["needs_words"]:
                with open(words_path, "w", encoding="utf-8") as f:
                    f.write(make_words_json(segments))
                log("  ✓ Words JSON saved.")

        # ── Caption burn ─────────────────────────────────────────────────
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
        self.work_items   = work_items
        self.new_3mb      = new_3mb
        self.root         = None
        self.log_text     = None
        self.status_label = None
        self.progress_bar = None
        self.done_btn     = None

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

    def _build_ui(self):
        root = tk.Tk()
        root.title("Foundry — Processing Videos")
        root.configure(bg=CF_BG)
        root.resizable(True, True)
        root.minsize(560, 420)

        w, h = 640, 540
        x    = (root.winfo_screenwidth()  - w) // 2
        y    = (root.winfo_screenheight() - h) // 2
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
            tk.Label(alert,
                     text=f"  ⚠  {len(self.new_3mb)} new 3MB file(s) detected — use Caption App (manual workflow)",
                     font=("Segoe UI", 9), anchor="w",
                     bg="#3A1A00", fg=CF_AMBER).pack(fill="x", pady=5, padx=8)

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
        self.progress_bar = ttk.Progressbar(root,
                                             style="F.Horizontal.TProgressbar",
                                             orient="horizontal",
                                             mode="determinate",
                                             maximum=max(len(self.work_items), 1))
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

        now = datetime.datetime.now().strftime("%Y-%m-%d %H:%M")
        log("┌─────────────────────────────────────────┐")
        log("│  Foundry Login Processor                │")
        log("│  The Candler Foundry                    │")
        log("└─────────────────────────────────────────┘")
        log(f"Started: {now}")
        log()

        self._set_status("Loading Whisper model...", CF_AMBER)
        log("Loading Whisper model (this may take a moment)...")
        try:
            import whisper
            model = whisper.load_model(WHISPER_MODEL)
            log(f"✓ Whisper {WHISPER_MODEL} loaded.\n")
        except ImportError:
            log("ERROR: Whisper not installed. Run:  pip install openai-whisper")
            self._set_status("Error: Whisper not installed.", CF_RED)
            write_log()
            return

        done   = 0
        errors = []

        for i, item in enumerate(self.work_items, 1):
            fname = os.path.basename(item["source"])
            label = f"[{i}/{len(self.work_items)}] {item['display_path']} — {item['base_name']}"
            log(label)
            self._set_status(label, CF_AMBER)

            missing = []
            if item["needs_srt"]:   missing.append("SRT")
            if item["needs_words"]: missing.append("Words JSON")
            if item["needs_cap"]:   missing.append("Captioned MP4")
            log(f"  Missing: {', '.join(missing)}")

            ok = process_item(item, model)
            if ok:
                done += 1
            else:
                errors.append(fname)

            self._set_progress(i)
            log()

        log("═" * 48)
        log(f"✓ Processed : {done}")
        log(f"  Errors    : {len(errors)}")
        for e in errors:
            log(f"    • {e}")
        log()
        log(f"Finished: {datetime.datetime.now().strftime('%Y-%m-%d %H:%M')}")

        if errors:
            self._set_status(
                f"Done — {done} processed, {len(errors)} error(s). Check log.", CF_RED)
        else:
            self._set_status(
                f"Done — {done} video(s) processed successfully.", CF_GREEN)

        mark_ran_today()
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
    new_3mb    = scan_3mb()

    if not work_items and not new_3mb:
        if not run_now:
            mark_ran_today()
        ctypes.windll.kernel32.SetThreadExecutionState(ES_CONTINUOUS)
        return

    StatusWindow(work_items, new_3mb).run()


if __name__ == "__main__":
    try:
        main()
    except Exception as e:
        import traceback
        err_path = os.path.join(SCRIPT_DIR, "foundry_launcher_error.txt")
        try:
            with open(err_path, "w") as f:
                f.write(traceback.format_exc())
        except Exception:
            pass
        try:
            r = tk.Tk()
            r.withdraw()
            mb.showerror("Foundry Processor Error",
                         f"An error occurred:\n\n{e}\n\nSee foundry_launcher_error.txt in Dropbox/Scripts.")
            r.destroy()
        except Exception:
            pass
