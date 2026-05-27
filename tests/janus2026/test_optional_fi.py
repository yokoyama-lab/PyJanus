from __future__ import annotations
import textwrap
from jana_py.cli import main

def test_optional_fi_modern(capsys, tmp_path):
    source = """
    void main() {
        int v;
        if (v = 0) {
            v += 0;
        } fi
        printf("%d\\n", v);
    }
    """
    path = tmp_path / "opt_fi.ja"
    path.write_text(textwrap.dedent(source))
    
    main([str(path)])
    out, err = capsys.readouterr()
    assert "0\n" in out

def test_optional_fi_modern_with_keyword(capsys, tmp_path):
    source = """
    void main() {
        int v;
        if (v = 0) {
            v += 0;
        } fi (v = 0)
        printf("%d\\n", v);
    }
    """
    path = tmp_path / "opt_fi_kw.ja"
    path.write_text(textwrap.dedent(source))
    
    main([str(path)])
    out, err = capsys.readouterr()
    assert "0\n" in out
