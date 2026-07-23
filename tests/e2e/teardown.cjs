module.exports = async () => {
  try {
    await fetch('http://127.0.0.1:4173/__e2e_shutdown', { method: 'POST' });
  } catch (_) {
    // The server may already have exited after an interrupted run.
  }
};
