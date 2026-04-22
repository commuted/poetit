# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Running the Application

```bash
python main.py
```

## Architecture

This is a single-file Python GUI application (`main.py`) built with `tkinter`. It is a minimal text editor with:

- A `tk.Text` widget as the main editing area (with undo support)
- A `File` menu with Open, Save As, and Exit commands
- File I/O using UTF-8 encoding

All logic lives in `main.py` — there are no modules, tests, or dependencies beyond the Python standard library.
