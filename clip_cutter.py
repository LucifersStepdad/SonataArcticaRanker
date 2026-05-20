"""
Sonata Arctica Clip Cutter - Enhanced Edition
===============================================
Features:
- Drag clip edges to resize (hover near edges)
- Mouse wheel to zoom timeline
- Shows current clip duration
"""

import os, sys, re, threading, time, unicodedata
import tkinter as tk
from tkinter import filedialog, messagebox, ttk
from pathlib import Path

# ── Dependency check ────────────────────────────────────────────
missing = []
try:
    import numpy as np
except ImportError:
    missing.append("numpy")
try:
    import sounddevice as sd
except ImportError:
    missing.append("sounddevice")
try:
    import soundfile as sf
except ImportError:
    missing.append("soundfile")
try:
    from pydub import AudioSegment
except ImportError:
    missing.append("pydub")

if missing:
    print(f"Missing: {', '.join(missing)}")
    print(f"Run:  pip install {' '.join(missing)}")
    sys.exit(1)

# ── Constants ───────────────────────────────────────────────────
DEFAULT_CLIP_DURATION = 5.0
MIN_CLIP_DURATION = 1.0
MAX_CLIP_DURATION = 15.0
AUDIO_EXTENSIONS = {".mp3", ".flac", ".wav", ".ogg", ".m4a", ".aac", ".wma"}

ALBUM_IDS = {
    "ecliptica": "ecliptica",
    "silence": "silence",
    "winterheart": "winterhearts",
    "reckoning": "reckoning",
    "unia": "unia",
    "days of grays": "daysofgrays",
    "grays": "daysofgrays",
    "stones": "stones",
    "pariah": "pariah",
    "ninth hour": "ninthhour",
    "ninth": "ninthhour",
    "talviy": "talviyo",
    "clear cold": "clearcold",
}

def slugify(text):
    text = unicodedata.normalize("NFKD", text).encode("ascii", "ignore").decode("ascii")
    text = "".join(c if c.isalnum() or c == " " else "" for c in text.lower()).strip()
    return "-".join(text.split())

def detect_album_id(folder):
    name = Path(folder).name.lower()
    for key, val in ALBUM_IDS.items():
        if key in name:
            return val
    return ""

def fmt(seconds):
    m = int(seconds) // 60
    s = seconds % 60
    return f"{m}:{s:05.2f}"

def fmt_duration(seconds):
    """Format duration nicely"""
    return f"{seconds:.1f}s"


# ── Audio engine ────────────────────────────────────────────────
class Player:
    def __init__(self):
        self.data = None
        self.samplerate = 44100
        self._stream = None
        self._cursor = 0
        self._lock = threading.Lock()
        self.playing = False
        self.on_stop = None

    def load(self, path: Path):
        self.stop()
        seg = AudioSegment.from_file(str(path))
        seg = seg.set_frame_rate(44100).set_sample_width(2)
        self.samplerate = 44100
        channels = seg.channels
        raw = np.frombuffer(seg.raw_data, dtype=np.int16).astype(np.float32) / 32768.0
        if channels == 2:
            self.data = raw.reshape(-1, 2)
        else:
            self.data = raw
        self.duration = len(self.data) / self.samplerate

    def play_from(self, start_sec: float, stop_after: float = None):
        self.stop()
        if self.data is None:
            return
        start_sample = int(max(0, start_sec) * self.samplerate)
        if stop_after is not None:
            end_sample = start_sample + int(stop_after * self.samplerate)
        else:
            end_sample = len(self.data)
        end_sample = min(end_sample, len(self.data))

        chunk = self.data[start_sample:end_sample]
        self._cursor = 0
        self._chunk = chunk
        self._play_start_wall = time.monotonic()
        self._play_start_sec = start_sec
        self.playing = True

        channels = chunk.shape[1] if chunk.ndim == 2 else 1

        def callback(outdata, frames, time_info, status):
            with self._lock:
                remaining = len(self._chunk) - self._cursor
                if remaining <= 0:
                    outdata[:] = 0
                    self.playing = False
                    raise sd.CallbackStop()
                n = min(frames, remaining)
                src = self._chunk[self._cursor:self._cursor + n]
                if channels == 1:
                    outdata[:n, 0] = src
                    if outdata.shape[1] == 2:
                        outdata[:n, 1] = src
                else:
                    outdata[:n] = src
                if n < frames:
                    outdata[n:] = 0
                self._cursor += n

        def finished():
            self.playing = False
            if self.on_stop:
                self.on_stop()

        self._stream = sd.OutputStream(
            samplerate=self.samplerate,
            channels=min(2, sd.query_devices(kind='output')['max_output_channels']),
            dtype='float32',
            callback=callback,
            finished_callback=finished,
            blocksize=1024,
        )
        self._stream.start()

    def stop(self):
        self.playing = False
        if self._stream is not None:
            try:
                self._stream.stop()
                self._stream.close()
            except Exception:
                pass
            self._stream = None

    def get_position(self):
        if not self.playing or self._chunk is None:
            return None
        elapsed = time.monotonic() - self._play_start_wall
        return self._play_start_sec + elapsed


# ── Main App ────────────────────────────────────────────────────
class ClipCutter(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("SA Clip Cutter - Enhanced")
        self.configure(bg="#050810")
        self.resizable(True, True)
        self.minsize(800, 600)

        self.player = Player()
        self.player.on_stop = self._on_playback_stopped

        self.songs: list[Path] = []
        self.song_index = 0
        self.album_id = ""
        self.output_dir: Path | None = None
        self.current_file: Path | None = None
        self.duration = 0.0
        self.clip_start = 0.0
        self.clip_duration = DEFAULT_CLIP_DURATION
        self._loading = False
        
        # Zoom/scroll state
        self.zoom_level = 1.0
        self.view_start = 0.0  # start time of visible area
        self.view_duration = 0.0  # how much time is visible
        
        # Resize tracking
        self.resizing = False
        self.resize_edge = None  # 'left' or 'right'
        
        self._build_ui()
        self.after(80, self._poll)
        self.protocol("WM_DELETE_WINDOW", self._quit)

    # ── UI ───────────────────────────────────────────────────────

    def _build_ui(self):
        # Top bar
        top = tk.Frame(self, bg="#050810")
        top.pack(fill="x", padx=16, pady=(16, 4))
        tk.Label(top, text="SONATA ARCTICA  //  CLIP CUTTER  [ENHANCED]",
                 bg="#050810", fg="#4a7ac8", font=("Courier New", 10, "bold")).pack(side="left")
        self.lbl_progress = tk.Label(top, text="", bg="#050810", fg="#4a5878",
                                     font=("Courier New", 10))
        self.lbl_progress.pack(side="right")

        # Folder row
        row1 = tk.Frame(self, bg="#050810")
        row1.pack(fill="x", padx=16, pady=4)
        self._btn("Open album folder", self._open_folder, row1).pack(side="left")
        tk.Label(row1, text="Album ID:", bg="#050810", fg="#8090b8",
                 font=("Courier New", 10)).pack(side="left", padx=(16, 4))
        self.album_var = tk.StringVar()
        tk.Entry(row1, textvariable=self.album_var, width=16,
                 bg="#0c1020", fg="#d0daf0", insertbackground="#7ab0f0",
                 relief="flat", font=("Courier New", 11),
                 highlightthickness=1, highlightbackground="#1a2a4a",
                 highlightcolor="#4a7ac8").pack(side="left", padx=4)
        tk.Label(row1, text="Output:", bg="#050810", fg="#8090b8",
                 font=("Courier New", 10)).pack(side="left", padx=(16, 4))
        self._btn("Choose…", self._choose_output, row1).pack(side="left")
        self.lbl_output = tk.Label(row1, text="(not set)", bg="#050810",
                                   fg="#4a5878", font=("Courier New", 9))
        self.lbl_output.pack(side="left", padx=8)

        # Song info
        info = tk.Frame(self, bg="#0c1020", highlightthickness=1,
                        highlightbackground="#131828")
        info.pack(fill="x", padx=16, pady=8)
        inner = tk.Frame(info, bg="#0c1020")
        inner.pack(fill="x", padx=16, pady=12)
        self.lbl_song = tk.Label(inner, text="— open a folder to begin —",
                                 bg="#0c1020", fg="#ffffff",
                                 font=("Georgia", 15, "bold"), anchor="w")
        self.lbl_song.pack(fill="x")
        self.lbl_album_info = tk.Label(inner, text="",
                                       bg="#0c1020", fg="#8090b8",
                                       font=("Georgia", 11, "italic"), anchor="w")
        self.lbl_album_info.pack(fill="x")

        # Timeline frame with zoom controls
        timeline_container = tk.Frame(self, bg="#050810")
        timeline_container.pack(fill="x", padx=16, pady=(4, 0))
        
        # Zoom controls
        zoom_frame = tk.Frame(timeline_container, bg="#050810")
        zoom_frame.pack(fill="x", pady=(0, 4))
        tk.Label(zoom_frame, text="Zoom:", bg="#050810", fg="#8090b8",
                 font=("Courier New", 9)).pack(side="left", padx=(0, 5))
        self._btn("−", lambda: self._zoom(-0.2), zoom_frame, padx=8, pady=2).pack(side="left", padx=2)
        self.zoom_label = tk.Label(zoom_frame, text="100%", bg="#050810", fg="#4a7ac8",
                                   font=("Courier New", 9), width=5)
        self.zoom_label.pack(side="left", padx=5)
        self._btn("+", lambda: self._zoom(0.2), zoom_frame, padx=8, pady=2).pack(side="left", padx=2)
        self._btn("Reset View", self._reset_view, zoom_frame, padx=10, pady=2).pack(side="left", padx=10)
        
        # Canvas
        self.canvas = tk.Canvas(timeline_container, bg="#0c1020", height=100,
                                highlightthickness=0, cursor="sb_h_double_arrow")
        self.canvas.pack(fill="x")
        
        # Bind canvas events
        self.canvas.bind("<ButtonPress-1>", self._canvas_press)
        self.canvas.bind("<B1-Motion>", self._canvas_drag)
        self.canvas.bind("<ButtonRelease-1>", self._canvas_release)
        self.canvas.bind("<Configure>", lambda e: self._draw_timeline())
        self.canvas.bind("<MouseWheel>", self._on_mousewheel)  # Windows
        self.canvas.bind("<Button-4>", self._on_mousewheel)    # Linux
        self.canvas.bind("<Button-5>", self._on_mousewheel)    # Linux

        # Time labels
        trow = tk.Frame(self, bg="#050810")
        trow.pack(fill="x", padx=16)
        self.lbl_start = tk.Label(trow, text="Start: 0:00.00", bg="#050810",
                                  fg="#c8a84a", font=("Courier New", 11, "bold"))
        self.lbl_start.pack(side="left")
        self.lbl_end = tk.Label(trow, text="End: 0:00.05", bg="#050810",
                                fg="#c8a84a", font=("Courier New", 11))
        self.lbl_end.pack(side="left", padx=10)
        self.lbl_dur = tk.Label(trow, text="", bg="#050810", fg="#4a5878",
                                font=("Courier New", 10))
        self.lbl_dur.pack(side="right")
        self.lbl_pos = tk.Label(trow, text="", bg="#050810", fg="#7ab0f0",
                                font=("Courier New", 10))
        self.lbl_pos.pack(side="right", padx=12)
        
        # Clip duration display
        self.lbl_clip_dur = tk.Label(trow, text="", bg="#050810", fg="#c8a84a",
                                     font=("Courier New", 10))
        self.lbl_clip_dur.pack(side="left", padx=20)

        # Duration slider for quick clip length adjustment
        dur_frame = tk.Frame(self, bg="#050810")
        dur_frame.pack(fill="x", padx=16, pady=(4, 0))
        tk.Label(dur_frame, text="Clip Length:", bg="#050810", fg="#8090b8",
                 font=("Courier New", 9)).pack(side="left", padx=(0, 8))
        self.dur_slider = tk.Scale(dur_frame, from_=MIN_CLIP_DURATION, to=MAX_CLIP_DURATION,
                                   orient="horizontal", resolution=0.5, length=200,
                                   bg="#050810", fg="#4a7ac8", highlightbackground="#1a2a4a",
                                   command=self._on_duration_change)
        self.dur_slider.set(DEFAULT_CLIP_DURATION)
        self.dur_slider.pack(side="left", padx=5)
        self.dur_label = tk.Label(dur_frame, text=f"{DEFAULT_CLIP_DURATION:.1f}s", 
                                  bg="#050810", fg="#c8a84a", font=("Courier New", 9))
        self.dur_label.pack(side="left", padx=5)

        # Playback controls
        ctrl = tk.Frame(self, bg="#050810")
        ctrl.pack(pady=8)
        self.btn_play = self._btn("▶  Play from here", self._play_from, ctrl)
        self.btn_play.pack(side="left", padx=5)
        self.btn_preview = self._btn("▶  Preview Clip", self._preview, ctrl)
        self.btn_preview.pack(side="left", padx=5)
        self._btn("■  Stop", self._stop, ctrl).pack(side="left", padx=5)

        # Fine adjust
        fine = tk.Frame(self, bg="#050810")
        fine.pack(pady=2)
        tk.Label(fine, text="Nudge Start:", bg="#050810", fg="#8090b8",
                 font=("Courier New", 10)).pack(side="left", padx=(0, 8))
        for lbl, d in [("◀◀ 5s", -5), ("◀ 1s", -1), ("◀ 0.1s", -0.1),
                       ("▶ 0.1s", 0.1), ("▶ 1s", 1), ("▶▶ 5s", 5)]:
            self._btn(lbl, lambda d=d: self._nudge(d), fine, padx=8).pack(side="left", padx=2)

        # Save / skip
        act = tk.Frame(self, bg="#050810")
        act.pack(pady=10)
        self._btn("✔  Save clip", self._save, act, color="#c8a84a").pack(side="left", padx=8)
        self._btn("→  Skip", self._skip, act).pack(side="left", padx=8)
        self._btn("←  Previous", self._prev, act).pack(side="left", padx=8)

        # Status
        self.lbl_status = tk.Label(self, text="Open an album folder to begin.",
                                   bg="#050810", fg="#8090b8",
                                   font=("Courier New", 10), wraplength=680)
        self.lbl_status.pack(pady=(0, 10))

        # Keyboard shortcuts
        self.bind("<Left>", lambda e: self._nudge(-0.1))
        self.bind("<Right>", lambda e: self._nudge(0.1))
        self.bind("<Shift-Left>", lambda e: self._nudge(-1))
        self.bind("<Shift-Right>", lambda e: self._nudge(1))
        self.bind("<space>", lambda e: self._preview())
        self.bind("<Return>", lambda e: self._save())
        self.bind("<Control-plus>", lambda e: self._zoom(0.2))
        self.bind("<Control-minus>", lambda e: self._zoom(-0.2))
        self.bind("<Control-0>", lambda e: self._reset_view())

    def _btn(self, text, cmd, parent, color="#7ab0f0", padx=12, pady=5):
        return tk.Button(parent, text=text, command=cmd,
                         bg="#0c1020", fg=color, activebackground="#131828",
                         activeforeground="#fff", relief="flat",
                         font=("Courier New", 10), padx=padx, pady=pady,
                         cursor="hand2", highlightthickness=1,
                         highlightbackground="#1a2a4a")

    # ── Zoom and view control ─────────────────────────────────────
    
    def _update_view(self):
        """Update view based on zoom level and clip position"""
        if self.duration <= 0:
            self.view_start = 0
            self.view_duration = self.duration
            return
        
        # Calculate view duration based on zoom
        self.view_duration = self.duration / self.zoom_level
        
        # Center view on clip start
        self.view_start = max(0, min(self.clip_start - (self.view_duration * 0.3),
                                     self.duration - self.view_duration))
        if self.view_start < 0:
            self.view_start = 0
        
        self._draw_timeline()
    
    def _zoom(self, delta):
        """Zoom in/out"""
        old_zoom = self.zoom_level
        self.zoom_level = max(1.0, min(20.0, self.zoom_level + delta))
        if self.zoom_level != old_zoom:
            self.zoom_label.config(text=f"{int(self.zoom_level * 100)}%")
            self._update_view()
    
    def _reset_view(self):
        """Reset zoom to normal"""
        self.zoom_level = 1.0
        self.zoom_label.config(text="100%")
        self._update_view()
    
    def _on_mousewheel(self, event):
        """Handle mouse wheel for zooming"""
        # Ctrl+wheel zooms
        if event.state & 0x0004:  # Ctrl key
            if event.delta > 0 or event.num == 4:
                self._zoom(0.1)
            else:
                self._zoom(-0.1)
            return "break"
    
    # ── File loading ─────────────────────────────────────────────

    def _open_folder(self):
        folder = filedialog.askdirectory(title="Select album folder")
        if not folder:
            return
        self.songs = sorted(
            [p for p in Path(folder).iterdir() if p.suffix.lower() in AUDIO_EXTENSIONS],
            key=lambda p: p.name)
        if not self.songs:
            messagebox.showerror("No audio files", "No supported audio files found.")
            return
        self.album_var.set(detect_album_id(folder))
        self.song_index = 0
        self._reset_view()
        self._load_song()

    def _choose_output(self):
        folder = filedialog.askdirectory(title="Select output (clips/) folder")
        if folder:
            self.output_dir = Path(folder)
            display = str(self.output_dir)
            if len(display) > 50:
                display = "…" + display[-48:]
            self.lbl_output.config(text=display)

    def _load_song(self):
        if self.song_index >= len(self.songs):
            self._all_done()
            return
        self._stop()
        self.current_file = self.songs[self.song_index]
        self.clip_start = 0.0
        self._reset_view()

        title = re.sub(r"^\d+[\s.\-_]+", "", self.current_file.stem).strip()
        self.lbl_song.config(text=title)
        self.lbl_album_info.config(text=f"loading…")
        self.lbl_status.config(text=f"Loading {self.current_file.name}…")
        self.lbl_progress.config(text=f"{self.song_index + 1} / {len(self.songs)}")
        self.update()

        self._loading = True
        threading.Thread(target=self._bg_load, daemon=True).start()

    def _bg_load(self):
        try:
            self.player.load(self.current_file)
            self.after(0, self._on_loaded)
        except Exception as e:
            self.after(0, lambda: self._set_status(f"Load error: {e}"))
            self._loading = False

    def _on_loaded(self):
        self._loading = False
        self.duration = self.player.duration
        album_id = self.album_var.get() or "?"
        self.lbl_album_info.config(text=album_id)
        self.lbl_dur.config(text=f"Duration: {fmt(self.duration)}")
        self._update_time_labels()
        self._update_view()
        self._set_status(f"Ready — Click/drag edges of yellow box to resize clip (currently {self.clip_duration:.1f}s)")

    # ── Timeline with resize handles ─────────────────────────────────

    def _canvas_press(self, event):
        """Handle mouse press on canvas - check if clicking on resize handles"""
        w = self.canvas.winfo_width()
        if w < 2 or self.duration <= 0:
            return
        
        # Calculate positions in time domain
        click_time = self._x_to_time(event.x)
        
        # Check if clicking near clip edges (within 5 pixels)
        start_x = self._time_to_x(self.clip_start)
        end_x = self._time_to_x(self.clip_start + self.clip_duration)
        
        if abs(event.x - start_x) < 8:
            self.resizing = True
            self.resize_edge = 'left'
            self.canvas.config(cursor="sb_h_double_arrow")
        elif abs(event.x - end_x) < 8:
            self.resizing = True
            self.resize_edge = 'right'
            self.canvas.config(cursor="sb_h_double_arrow")
        else:
            # Normal seek
            self._seek_to_time(click_time)
    
    def _canvas_drag(self, event):
        """Handle drag for resizing or seeking"""
        if self.resizing:
            w = self.canvas.winfo_width()
            if w < 2 or self.duration <= 0:
                return
            
            drag_time = self._x_to_time(event.x)
            
            if self.resize_edge == 'left':
                new_start = max(0, min(drag_time, self.clip_start + self.clip_duration - MIN_CLIP_DURATION))
                if new_start != self.clip_start:
                    self.clip_start = new_start
                    self.clip_duration = min(self.clip_duration + (self.clip_start - new_start), 
                                            self.duration - self.clip_start)
                    self.clip_duration = max(MIN_CLIP_DURATION, min(MAX_CLIP_DURATION, self.clip_duration))
                    self.dur_slider.set(self.clip_duration)
                    self.dur_label.config(text=f"{self.clip_duration:.1f}s")
                    self._update_time_labels()
                    self._draw_timeline()
                    
            elif self.resize_edge == 'right':
                new_end = max(self.clip_start + MIN_CLIP_DURATION, 
                             min(drag_time, self.clip_start + MAX_CLIP_DURATION, self.duration))
                self.clip_duration = max(MIN_CLIP_DURATION, min(MAX_CLIP_DURATION, new_end - self.clip_start))
                self.dur_slider.set(self.clip_duration)
                self.dur_label.config(text=f"{self.clip_duration:.1f}s")
                self._update_time_labels()
                self._draw_timeline()
        else:
            # Normal seeking
            drag_time = self._x_to_time(event.x)
            self._seek_to_time(drag_time)
    
    def _canvas_release(self, event):
        """Release resize mode"""
        self.resizing = False
        self.resize_edge = None
        self.canvas.config(cursor="sb_h_double_arrow")
    
    def _x_to_time(self, x):
        """Convert canvas x coordinate to time"""
        w = self.canvas.winfo_width()
        if w < 2:
            return 0
        fraction = max(0, min(1, x / w))
        return self.view_start + (fraction * self.view_duration)
    
    def _time_to_x(self, time):
        """Convert time to canvas x coordinate"""
        w = self.canvas.winfo_width()
        if w < 2 or self.view_duration <= 0:
            return 0
        if time < self.view_start:
            return 0
        if time > self.view_start + self.view_duration:
            return w
        fraction = (time - self.view_start) / self.view_duration
        return int(fraction * w)
    
    def _seek_to_time(self, time):
        """Seek to a specific time"""
        time = max(0, min(time, self.duration - self.clip_duration))
        self.clip_start = time
        self._draw_timeline()
        self._update_time_labels()
    
    def _on_duration_change(self, val):
        """Called when duration slider changes"""
        self.clip_duration = max(MIN_CLIP_DURATION, min(MAX_CLIP_DURATION, float(val)))
        # Ensure clip doesn't go past song end
        if self.clip_start + self.clip_duration > self.duration:
            self.clip_start = max(0, self.duration - self.clip_duration)
        self.dur_label.config(text=f"{self.clip_duration:.1f}s")
        self._update_time_labels()
        self._draw_timeline()

    def _draw_timeline(self):
        """Draw the timeline with zoom and resize handles"""
        c = self.canvas
        w = c.winfo_width()
        h = c.winfo_height()
        if w < 2 or self.duration <= 0:
            return
        c.delete("all")
        c.create_rectangle(0, 0, w, h, fill="#0c1020", outline="")

        # Draw background grid based on view range
        view_end = self.view_start + self.view_duration
        
        # Determine tick interval based on zoom level
        if self.view_duration < 10:
            tick_interval = 1
        elif self.view_duration < 30:
            tick_interval = 2
        elif self.view_duration < 60:
            tick_interval = 5
        else:
            tick_interval = 10
        
        # Draw time markers
        t = int(self.view_start / tick_interval) * tick_interval
        while t <= view_end:
            if self.view_start <= t <= view_end:
                x = self._time_to_x(t)
                c.create_line(x, h, x, h - 12, fill="#1e2e4e", width=1)
                c.create_text(x, h - 18, text=fmt(t), fill="#4a5878",
                              font=("Courier New", 7), anchor="s")
            t += tick_interval

        # Draw clip region
        clip_end = self.clip_start + self.clip_duration
        x1 = self._time_to_x(self.clip_start)
        x2 = self._time_to_x(clip_end)
        
        # Only draw if visible
        if x2 > 0 and x1 < w:
            x1_draw = max(0, x1)
            x2_draw = min(w, x2)
            c.create_rectangle(x1_draw, 0, x2_draw, h, fill="#182810", outline="")
            c.create_rectangle(x1_draw, 0, x2_draw, h, fill="", outline="#c8a84a", width=2)
            
            # Draw resize handles
            if x1 >= 0 and x1 <= w:
                c.create_rectangle(x1-3, 0, x1+3, h, fill="#c8a84a", outline="")
            if x2 >= 0 and x2 <= w:
                c.create_rectangle(x2-3, 0, x2+3, h, fill="#c8a84a", outline="")

        # Draw playhead
        pos = self.player.get_position()
        if pos is not None:
            xp = self._time_to_x(pos)
            if 0 <= xp <= w:
                c.create_line(xp, 0, xp, h, fill="#7ab0f0", width=1, dash=(4, 3))

        # Show time at left edge
        c.create_text(6, 6, text=fmt(self.clip_start), fill="#c8a84a",
                      font=("Courier New", 9), anchor="nw")
        
        # Show zoom range indicator
        zoom_text = f"View: {fmt(self.view_start)} - {fmt(view_end)}"
        c.create_text(w-6, 6, text=zoom_text, fill="#4a5878",
                      font=("Courier New", 8), anchor="ne")

    def _update_time_labels(self):
        """Update time display labels"""
        self.lbl_start.config(text=f"Start: {fmt(self.clip_start)}")
        self.lbl_end.config(text=f"End: {fmt(self.clip_start + self.clip_duration)}")
        self.lbl_clip_dur.config(text=f"Clip: {fmt_duration(self.clip_duration)}")

    def _nudge(self, delta):
        if self.duration <= 0:
            return
        pos = max(0.0, min(self.clip_start + delta, self.duration - self.clip_duration))
        self.clip_start = pos
        self._draw_timeline()
        self._update_time_labels()

    # ── Playback ─────────────────────────────────────────────────

    def _play_from(self):
        if self._loading or self.player.data is None:
            return
        self.player.play_from(self.clip_start)
        self.btn_play.config(text="▶  Playing…")

    def _preview(self):
        if self._loading or self.player.data is None:
            return
        self.player.play_from(self.clip_start, stop_after=self.clip_duration)
        self.btn_preview.config(text="▶  Previewing…")

    def _stop(self):
        self.player.stop()
        self._reset_btn_labels()

    def _on_playback_stopped(self):
        self.after(0, self._reset_btn_labels)

    def _reset_btn_labels(self):
        self.btn_play.config(text="▶  Play from here")
        self.btn_preview.config(text="▶  Preview Clip")

    def _poll(self):
        pos = self.player.get_position()
        if pos is not None:
            self.lbl_pos.config(text=f"▶ {fmt(pos)}")
            self._draw_timeline()
        else:
            self.lbl_pos.config(text="")
        self.after(80, self._poll)

    # ── Save / navigate ──────────────────────────────────────────

    def _save(self):
        if not self.current_file or self._loading:
            return
        album_id = self.album_var.get().strip()
        if not album_id:
            messagebox.showwarning("Album ID missing", "Enter the album ID before saving.")
            return
        if not self.output_dir:
            messagebox.showwarning("No output folder", "Choose an output folder first.")
            return

        title = re.sub(r"^\d+[\s.\-_]+", "", self.current_file.stem).strip()
        slug = slugify(title)
        out_name = f"{album_id}--{slug}.mp3"
        out_path = self.output_dir / out_name
        self._set_status(f"Exporting {out_name}…")
        self.update()

        start_ms = int(self.clip_start * 1000)
        end_ms = start_ms + int(self.clip_duration * 1000)

        def do_export():
            try:
                seg = AudioSegment.from_file(str(self.current_file))
                seg[start_ms:end_ms].export(str(out_path), format="mp3", bitrate="192k")
                self.after(0, lambda: self._saved(out_name))
            except Exception as e:
                self.after(0, lambda: self._set_status(f"Export failed: {e}"))

        threading.Thread(target=do_export, daemon=True).start()

    def _saved(self, name):
        self._set_status(f"✔  Saved  {name}")
        self._advance()

    def _skip(self):
        self._set_status(f"Skipped.")
        self._advance()

    def _prev(self):
        if self.song_index > 0:
            self.song_index -= 1
            self._load_song()

    def _advance(self):
        self._stop()
        self.song_index += 1
        if self.song_index >= len(self.songs):
            self._all_done()
        else:
            self._load_song()

    def _all_done(self):
        self.lbl_song.config(text="— all songs done —")
        self.lbl_album_info.config(text="")
        self._set_status("✔  Album complete! Open another folder to continue.")

    def _set_status(self, msg):
        self.lbl_status.config(text=msg)

    def _quit(self):
        self.player.stop()
        self.destroy()


if __name__ == "__main__":
    app = ClipCutter()
    app.mainloop()