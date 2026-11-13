<?php
/* Apache/PHP gateway for the shared, restricted Python playground backend.
 * Requires python3, coreutils timeout, and Unix resource limits/flock.
 * Configure PYJANUS_ROOT, PYJANUS_PYTHON and PYJANUS_SAVES via the environment.
 */
$PYJANUS_ROOT = getenv('PYJANUS_ROOT') ?: dirname(__DIR__);
$PYTHON = getenv('PYJANUS_PYTHON') ?: 'python3';
$MAX_REQUEST = 256 * 1024;
$MAX_RESPONSE = 16 * 1024 * 1024;
$method = $_SERVER['REQUEST_METHOD'];
header('X-Content-Type-Options: nosniff');

function reject_request(int $status, string $message): void {
    http_response_code($status);
    header('Content-Type: application/json');
    echo json_encode(['error' => $message]);
    exit;
}

if ($method === 'POST') {
    $type = strtolower(trim(explode(';', $_SERVER['CONTENT_TYPE'] ?? '')[0]));
    if ($type !== 'application/json') reject_request(415, 'application/json required');
    $length = $_SERVER['CONTENT_LENGTH'] ?? '';
    if (!ctype_digit((string)$length)) reject_request(400, 'invalid content length');
    if ((float)$length > $MAX_REQUEST) reject_request(413, 'request too large');
    $body = file_get_contents('php://input', false, null, 0, $MAX_REQUEST + 1);
    if ($body === false || strlen($body) !== (int)$length) reject_request(400, 'invalid request');
    if (strlen($body) > $MAX_REQUEST) reject_request(413, 'request too large');
    json_decode($body);
    if (json_last_error() !== JSON_ERROR_NONE) reject_request(400, 'invalid JSON');
} elseif ($method === 'GET') {
    $body = $_SERVER['QUERY_STRING'] ?? '';
    if (strlen($body) > $MAX_REQUEST) reject_request(413, 'query too large');
} else {
    reject_request(405, 'method not allowed');
}

// Files avoid pipe deadlocks when both stdout and stderr are written. The
// Python backend caps execution output and handles all input/path validation,
// save quotas, cross-process run slots, and HTML-safe JSON serialization.
$input = tmpfile(); $output = tmpfile(); $errors = tmpfile();
if ($input === false || $output === false || $errors === false) {
    reject_request(503, 'execution unavailable');
}
fwrite($input, $body);
rewind($input);
$argv = ['timeout', '-k', '2', '15', $PYTHON, '-m', 'jana_py.web', '--gateway', $method];
// Apache SetEnv values may be request-local rather than inherited by children.
$env = getenv();
$env['PYJANUS_SAVES'] = getenv('PYJANUS_SAVES') ?: $PYJANUS_ROOT.'/playground-saves';
$proc = proc_open($argv, [0 => $input, 1 => $output, 2 => $errors], $pipes, $PYJANUS_ROOT, $env);
if (!is_resource($proc)) reject_request(503, 'execution unavailable');
$code = proc_close($proc);
rewind($output);
$response = stream_get_contents($output, $MAX_RESPONSE + 1);
fclose($input); fclose($output); fclose($errors);
if ($code !== 0 || $response === false || strlen($response) > $MAX_RESPONSE) {
    reject_request(503, 'request failed or execution limit exceeded');
}
header('Content-Type: '.($method === 'GET' ? 'text/html; charset=utf-8' : 'application/json'));
echo $response;
