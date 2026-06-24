# PyJanus web playground

A small browser playground for PyJanus: edit a Janus program, pick the dialect
(`--std`), direction and mode, supply `read`/`scanf` input, and run it — output and
errors come straight back.  It is the PyJanus counterpart of Jana-JanusInterp's web
UI.

The front-end (`playground.html`) and the example programs (`examples.json`) are
**shared** by two interchangeable backends:

| backend | how to run | needs |
|---------|-----------|-------|
| **Python** (stdlib only) | `python3 -m jana_py.web` | just Python (no extra deps) |
| **Apache / PHP** | drop `webui/` in the docroot | PHP + `python3` + `timeout` |

Both serve the same page and run programs by shelling out to
`python -m jana_py.cli` with a per-run timeout.

## Option 1 — Python server (no dependencies)

```bash
python3 -m jana_py.web                 # http://127.0.0.1:8000
python3 -m jana_py.web --host 0.0.0.0 --port 9000
```

## Option 2 — Apache + PHP

Copy this `webui/` directory under your web root (or alias a vhost to it):

```apache
# e.g. in a vhost / .conf
Alias /pyjanus /srv/PyJanus/webui
<Directory /srv/PyJanus/webui>
    Require all granted
    DirectoryIndex index.php
    SetEnv PYJANUS_ROOT /srv/PyJanus      # dir that contains jana_py/
    SetEnv PYJANUS_PYTHON /usr/bin/python3
</Directory>
```

Then open `http://your-host/pyjanus/`.  Requirements on the server:

- PHP with `proc_open` enabled (the default),
- `python3` on `PATH` (or set `PYJANUS_PYTHON`) with the `jana_py` package
  importable from `PYJANUS_ROOT` (the directory that contains `jana_py/`),
- the `timeout` command (coreutils) — used for the hard per-run cap.

Defaults if the env vars are unset: `PYJANUS_ROOT` = the parent of `webui/`,
`PYJANUS_PYTHON` = `python3`.  Quick local check without Apache:

```bash
php -S 127.0.0.1:8080 -t webui          # then open http://127.0.0.1:8080/
```

## Files

| file | role |
|------|------|
| `playground.html` | shared front-end (placeholders `%%EXAMPLES%%`, `%%STDS%%`) |
| `examples.json`   | shared example programs + the dialect list |
| `index.php`       | PHP backend (GET = page, POST = run) |
| `../jana_py/web.py` | Python backend (`python -m jana_py.web`) |

To add an example or change the UI, edit `examples.json` / `playground.html`
once — both backends pick it up.

## Notes / security

- Each run is capped at **10 s** (Python: `subprocess` timeout; PHP: `timeout`).
- Janus is a small, pure reversible language — no file system or network access —
  so running submitted programs is comparatively safe; still, expose this only to
  trusted users (it does spawn a Python process per run).
- Inputs are validated server-side (`--std` against the known list, `-m`/`-p`
  digits only) and the program source is written to a temp file (never shell-
  interpolated); all argv elements are `escapeshellarg`'d in the PHP backend.
