<?php
/*
 * PyJanus web playground — Apache/PHP deployment.
 *
 * Drop the `webui/` directory in your docroot (or point a vhost at it).  Needs:
 *   - PHP with proc_open enabled,
 *   - python3 reachable, with the `jana_py` package importable from PYJANUS_ROOT,
 *   - the `timeout` command (coreutils) for the per-run hard cap.
 *
 * Configure via env (e.g. SetEnv in Apache) or edit the defaults below:
 *   PYJANUS_ROOT   directory that contains jana_py/  (default: parent of webui/)
 *   PYJANUS_PYTHON python interpreter               (default: python3)
 *
 * Serves the shared front-end (playground.html + examples.json) on GET and runs
 * a program on POST — the same UI as `python -m jana_py.web`.
 */

$PYJANUS_ROOT = getenv('PYJANUS_ROOT') ?: dirname(__DIR__);
$PYTHON       = getenv('PYJANUS_PYTHON') ?: 'python3';
$SAVES_DIR    = getenv('PYJANUS_SAVES') ?: dirname(__DIR__).'/playground-saves';
$TIMEOUT      = 10;  // seconds, hard cap per run
$STDS  = ['janus2026','jana2014','jana2014basic','jana2014_in_out','janus1982','janus1982ext'];
$MODES = ['run'=>[], 'store'=>['-s'], 'invert'=>['-i'], 'ast'=>['-a'], 'cpp'=>['-c'],
          'debug'=>['-d'], 'circuit'=>['--circuit'], 'profile'=>['--profile']];
$JSON  = JSON_UNESCAPED_UNICODE | JSON_UNESCAPED_SLASHES;

if ($_SERVER['REQUEST_METHOD'] === 'POST') {
    header('Content-Type: application/json');
    $req = json_decode(file_get_contents('php://input'), true);
    if (!is_array($req)) $req = [];
    $out = (($req['action'] ?? '') === 'save') ? save_state($req['state'] ?? []) : run_pyjanus($req);
    echo json_encode($out, $JSON);
    exit;
}

// GET: serve the page with examples/stds (and any saved program ?p=hash) injected
$html = @file_get_contents(__DIR__.'/playground.html');
$data = json_decode(@file_get_contents(__DIR__.'/examples.json'), true);
if ($html === false || !is_array($data)) {
    http_response_code(500);
    exit("missing webui asset (playground.html / examples.json)");
}
$saved = 'null';
if (isset($_GET['p']) && preg_match('/^[a-f0-9]{6,16}$/', $_GET['p'])) {
    $f = $SAVES_DIR.'/'.$_GET['p'].'.json';
    if (is_file($f)) { $c = file_get_contents($f); if ($c !== false && $c !== '') $saved = $c; }
}
$html = str_replace('%%SAVED%%',    $saved, $html);
$html = str_replace('%%EXAMPLES%%', json_encode($data['examples'], $JSON), $html);
$html = str_replace('%%STDS%%',     json_encode($data['stds'], $JSON),     $html);
header('Content-Type: text/html; charset=utf-8');
echo $html;
exit;

// Store a program state under a short content hash; returns ['id'=>hash].
function save_state($state): array {
    global $SAVES_DIR, $STDS, $JSON;
    if (!is_array($state)) return ['error' => 'bad request'];
    $clean = [];
    foreach (['source','std','mode','dir','args','mbits','mprime'] as $k) {
        $clean[$k] = (string)($state[$k] ?? '');
    }
    if (strlen($clean['source']) > 65536) return ['error' => 'program too large'];
    if (!in_array($clean['std'], $STDS, true)) $clean['std'] = 'janus2026';
    $body = json_encode($clean, $JSON);
    $id = substr(hash('sha256', $body), 0, 10);     // short, content-addressed
    if (!is_dir($SAVES_DIR)) @mkdir($SAVES_DIR, 0775, true);
    if (@file_put_contents($SAVES_DIR.'/'.$id.'.json', $body) === false) {
        return ['error' => 'cannot write save'];
    }
    return ['id' => $id];
}

function run_pyjanus(array $req): array {
    global $PYJANUS_ROOT, $PYTHON, $TIMEOUT, $STDS, $MODES;

    $std  = in_array(($req['std'] ?? ''), $STDS, true) ? $req['std'] : 'janus2026';
    $dir  = (($req['direction'] ?? '') === 'backward') ? 'backward' : 'forward';
    $mode = $req['mode'] ?? 'run';
    $flags = $MODES[$mode] ?? [];
    $flags[] = '--direction'; $flags[] = $dir;
    $mb = trim($req['modBits'] ?? '');   if ($mb !== '' && ctype_digit($mb)) { $flags[]='-m'; $flags[]=$mb; }
    $mp = trim($req['modPrime'] ?? '');  if ($mp !== '' && ctype_digit($mp)) { $flags[]='-p'; $flags[]=$mp; }
    if (in_array($mode, ['ast','invert','cpp'], true)) $flags[] = '--no-main';

    $tmp = tempnam(sys_get_temp_dir(), 'ja_');
    file_put_contents($tmp, (string)($req['source'] ?? ''));

    // Array form of proc_open => executed directly, WITHOUT a shell, so no shell
    // injection is possible (each element is an exec argument).  `timeout` is the
    // hard cap; the 4th arg sets cwd so `-m jana_py.cli` resolves.
    $argv = array_merge(['timeout', (string)intval($TIMEOUT), $PYTHON, '-m', 'jana_py.cli',
                         '--std', $std], $flags, [$tmp]);
    foreach (preg_split('/\s+/', trim($req['args'] ?? ''), -1, PREG_SPLIT_NO_EMPTY) as $a) {
        $argv[] = $a;  // each value -> one scanf/read line on stdin
    }

    $stdout = $stderr = ''; $code = 1;
    $proc = proc_open($argv, [1=>['pipe','w'], 2=>['pipe','w']], $pipes, $PYJANUS_ROOT);
    if (is_resource($proc)) {
        $stdout = stream_get_contents($pipes[1]); fclose($pipes[1]);
        $stderr = stream_get_contents($pipes[2]); fclose($pipes[2]);
        $code   = proc_close($proc);
    }
    @unlink($tmp);
    if ($code === 124) $stderr = "timed out after {$TIMEOUT}s\n".$stderr;

    $shown = 'pyjanus --std '.$std.' '.implode(' ', $flags);
    if (trim($req['args'] ?? '') !== '') $shown .= ' …args…';
    return ['stdout'=>$stdout, 'stderr'=>$stderr, 'code'=>$code, 'cmd'=>$shown];
}
