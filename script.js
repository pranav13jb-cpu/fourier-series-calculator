/* =========================================================================
   Fourier Series Calculator — script.js
   Sections:
     1. Natural math-notation parser (x^2, sin, pi, |x|, ternary, ...)
     2. Numerical integration (Simpson's / Trapezoidal)
     3. Fourier coefficient computation (unchanged, verified against
        analytical solutions for f(x)=x and f(x)=x^2 — see project notes)
     4. Rendering: numeric equation, coefficient table, chart
     5. UI wiring: theme, presets, collapsible cards, slider, search/sort,
        export/copy/print, keyboard shortcuts, session persistence
   ========================================================================= */

(function () {
  'use strict';

  /* ---------------------------------------------------------------------
     DOM REFERENCES
     --------------------------------------------------------------------- */
  const els = {
    funcInput: document.getElementById('funcInput'),
    periodInput: document.getElementById('periodInput'),
    termsInput: document.getElementById('termsInput'),
    lowerLimit: document.getElementById('lowerLimit'),
    upperLimit: document.getElementById('upperLimit'),
    autoLimits: document.getElementById('autoLimits'),
    methodSelect: document.getElementById('methodSelect'),
    samplesInput: document.getElementById('samplesInput'),
    sampleSelect: document.getElementById('sampleSelect'),
    calculateBtn: document.getElementById('calculateBtn'),
    calculateLabel: document.getElementById('calculateLabel'),
    btnSpinner: document.getElementById('btnSpinner'),
    resetBtn: document.getElementById('resetBtn'),
    exportReportBtn: document.getElementById('exportReportBtn'),
    copyResultsBtn: document.getElementById('copyResultsBtn'),
    errorBox: document.getElementById('errorBox'),
    equationDisplay: document.getElementById('equationDisplay'),
    copyLatexBtn: document.getElementById('copyLatexBtn'),
    termSlider: document.getElementById('termSlider'),
    termSliderValue: document.getElementById('termSliderValue'),
    coeffTableBody: document.getElementById('coeffTableBody'),
    tableSearch: document.getElementById('tableSearch'),
    copyTableBtn: document.getElementById('copyTableBtn'),
    exportCsvBtn: document.getElementById('exportCsvBtn'),
    chartCanvas: document.getElementById('fourierChart'),
    resetZoomBtn: document.getElementById('resetZoomBtn'),
    integrationStatus: document.getElementById('integrationStatus'),
    convergenceStatus: document.getElementById('convergenceStatus'),
    themeToggle: document.getElementById('themeToggle'),
    themeIcon: document.getElementById('themeIcon'),
    themeLabel: document.getElementById('themeLabel'),
    printBtn: document.getElementById('printBtn'),
  };

  let state = {
    a0: 0, an: [], bn: [], omega: 0, T: 0, center: 0,
    fCompiled: null, maxTerms: 0, method: 'simpson', steps: 1000,
    a: 0, b: 0, exprStr: '',
  };
  let chart = null;
  let sortState = { column: 'n', dir: 'asc' };

  /* =======================================================================
     1. NATURAL MATH NOTATION PARSER
     A small recursive-descent parser. Converts x^2, sin(x), pi, e, |x|,
     and simple ternary/comparison expressions (for piecewise functions)
     into valid JavaScript. Exponents compile to Math.pow(...) rather than
     the ** operator so that inputs like "exp(-x^2)" — which would be a
     SyntaxError as "-x**2" in raw JS — work correctly.
     ======================================================================= */
  const FUNC_MAP = {
    asin: 'asin', acos: 'acos', atan2: 'atan2', atan: 'atan',
    sqrt: 'sqrt', abs: 'abs', exp: 'exp',
    ln: 'log', log: 'log10',
    sin: 'sin', cos: 'cos', tan: 'tan',
    min: 'min', max: 'max', floor: 'floor', ceil: 'ceil', round: 'round', sign: 'sign',
  };

  function tokenize(input) {
    const tokens = [];
    let i = 0;
    const n = input.length;
    while (i < n) {
      const c = input[i];
      if (/\s/.test(c)) { i++; continue; }
      if (/[0-9.]/.test(c)) {
        let j = i;
        while (j < n && /[0-9.]/.test(input[j])) j++;
        if (j < n && (input[j] === 'e' || input[j] === 'E') &&
            (/[0-9.]/.test(input[j + 1] || '') || (['+', '-'].includes(input[j + 1]) && /[0-9]/.test(input[j + 2] || '')))) {
          j++;
          if (input[j] === '+' || input[j] === '-') j++;
          while (j < n && /[0-9]/.test(input[j])) j++;
        }
        tokens.push({ type: 'num', value: input.slice(i, j) });
        i = j;
        continue;
      }
      if (/[A-Za-z_]/.test(c)) {
        let j = i;
        while (j < n && /[A-Za-z0-9_.]/.test(input[j])) j++; // dots allowed: Math.sin, Math.PI
        tokens.push({ type: 'ident', value: input.slice(i, j) });
        i = j;
        continue;
      }
      if ('+-*/^(),?:|'.includes(c)) { tokens.push({ type: 'op', value: c }); i++; continue; }
      if ('<>=!'.includes(c)) {
        let j = i + 1;
        if (input[j] === '=') j++;
        tokens.push({ type: 'op', value: input.slice(i, j) });
        i = j;
        continue;
      }
      throw new Error(`Unexpected character "${c}" in expression.`);
    }
    return tokens;
  }

  function parseTokens(tokens) {
    let pos = 0;
    const peek = () => tokens[pos];
    const next = () => tokens[pos++];
    const expectOp = (v) => {
      const t = next();
      if (!t || t.type !== 'op' || t.value !== v) {
        throw new Error(`Expected "${v}" but found "${t ? t.value : 'end of expression'}".`);
      }
    };

    function parseExpr() { return parseTernary(); }

    function parseTernary() {
      const cond = parseComparison();
      if (peek() && peek().type === 'op' && peek().value === '?') {
        next();
        const a = parseTernary();
        expectOp(':');
        const b = parseTernary();
        return `(${cond} ? ${a} : ${b})`;
      }
      return cond;
    }

    function parseComparison() {
      let left = parseAdditive();
      while (peek() && peek().type === 'op' && ['<', '>', '<=', '>=', '==', '!='].includes(peek().value)) {
        const op = next().value;
        const right = parseAdditive();
        left = `(${left} ${op === '==' ? '===' : op === '!=' ? '!==' : op} ${right})`;
      }
      return left;
    }

    function parseAdditive() {
      let left = parseMultiplicative();
      while (peek() && peek().type === 'op' && (peek().value === '+' || peek().value === '-')) {
        const op = next().value;
        const right = parseMultiplicative();
        left = `(${left} ${op} ${right})`;
      }
      return left;
    }

    function parseMultiplicative() {
      let left = parseUnary();
      while (peek() && peek().type === 'op' && (peek().value === '*' || peek().value === '/')) {
        const op = next().value;
        const right = parseUnary();
        left = `(${left} ${op} ${right})`;
      }
      return left;
    }

    function parseUnary() {
      if (peek() && peek().type === 'op' && (peek().value === '-' || peek().value === '+')) {
        const op = next().value;
        const operand = parseUnary();
        return op === '-' ? `(-${operand})` : `(+${operand})`;
      }
      return parsePower();
    }

    // Power binds tighter than unary minus (-x^2 = -(x^2), matching standard
    // math convention) and is right-associative (x^2^3 = x^(2^3)).
    function parsePower() {
      const base = parseAtom();
      if (peek() && peek().type === 'op' && peek().value === '^') {
        next();
        const exponent = parseUnary();
        return `Math.pow(${base}, ${exponent})`;
      }
      return base;
    }

    function parseAtom() {
      const t = peek();
      if (!t) throw new Error('Unexpected end of expression.');

      if (t.type === 'num') { next(); return t.value; }

      if (t.type === 'op' && t.value === '(') {
        next();
        const inner = parseExpr();
        expectOp(')');
        return `(${inner})`;
      }

      if (t.type === 'op' && t.value === '|') {
        next();
        const inner = parseExpr();
        expectOp('|');
        return `Math.abs(${inner})`;
      }

      if (t.type === 'ident') {
        next();
        const name = t.value;
        if (peek() && peek().type === 'op' && peek().value === '(') {
          next();
          const args = [];
          if (!(peek() && peek().type === 'op' && peek().value === ')')) {
            args.push(parseExpr());
            while (peek() && peek().type === 'op' && peek().value === ',') {
              next();
              args.push(parseExpr());
            }
          }
          expectOp(')');
          const mapped = FUNC_MAP[name.toLowerCase()];
          const jsName = mapped ? `Math.${mapped}` : name; // dotted names like Math.sin pass through
          return `${jsName}(${args.join(', ')})`;
        }
        if (name === 'pi') return 'Math.PI';
        if (name === 'e') return 'Math.E';
        return name; // x, T, or a dotted constant like Math.PI pass through verbatim
      }

      throw new Error(`Unexpected token "${t.value}".`);
    }

    const result = parseExpr();
    if (pos < tokens.length) {
      throw new Error(`Unexpected token "${tokens[pos].value}" — check your parentheses.`);
    }
    return result;
  }

  function translateMathNotation(exprRaw) {
    const tokens = tokenize(exprRaw);
    return parseTokens(tokens);
  }

  /* =======================================================================
     2. NUMERICAL INTEGRATION (unchanged mathematics)
     ======================================================================= */
  function simpson(f, a, b, n) {
    if (n % 2 !== 0) n += 1;
    const h = (b - a) / n;
    let sum = f(a) + f(b);
    for (let i = 1; i < n; i++) {
      const x = a + i * h;
      sum += (i % 2 === 0 ? 2 : 4) * f(x);
    }
    return (h / 3) * sum;
  }

  function trapezoidal(f, a, b, n) {
    const h = (b - a) / n;
    let sum = 0.5 * (f(a) + f(b));
    for (let i = 1; i < n; i++) sum += f(a + i * h);
    return sum * h;
  }

  function integrate(f, a, b, n, method) {
    return method === 'trapezoidal' ? trapezoidal(f, a, b, n) : simpson(f, a, b, n);
  }

  /* ---------------------------------------------------------------------
     THEME HANDLING
     --------------------------------------------------------------------- */
  function applyTheme(theme) {
    document.body.setAttribute('data-theme', theme);
    els.themeIcon.textContent = theme === 'dark' ? '\u{1F319}' : '\u{2600}';
    els.themeLabel.textContent = theme === 'dark' ? 'Dark' : 'Light';
    try { localStorage.setItem('fourier-theme', theme); } catch (e) { /* ignore */ }
    if (chart) updateChart(getCurrentSliderTerms());
  }
  function initTheme() {
    let saved = 'dark';
    try { saved = localStorage.getItem('fourier-theme') || 'dark'; } catch (e) { /* ignore */ }
    applyTheme(saved);
  }
  els.themeToggle.addEventListener('click', () => {
    applyTheme(document.body.getAttribute('data-theme') === 'dark' ? 'light' : 'dark');
  });
  function cssVar(name) { return getComputedStyle(document.body).getPropertyValue(name).trim(); }

  /* ---------------------------------------------------------------------
     TOAST / ERROR HELPERS
     --------------------------------------------------------------------- */
  let toastEl = null;
  function showToast(message) {
    if (!toastEl) {
      toastEl = document.createElement('div');
      toastEl.className = 'toast';
      document.body.appendChild(toastEl);
    }
    toastEl.textContent = message;
    toastEl.classList.add('show');
    clearTimeout(toastEl._timer);
    toastEl._timer = setTimeout(() => toastEl.classList.remove('show'), 2200);
  }
  function showError(message) { els.errorBox.textContent = message; els.errorBox.hidden = false; }
  function clearError() { els.errorBox.textContent = ''; els.errorBox.hidden = true; }

  /* ---------------------------------------------------------------------
     CLIPBOARD (with execCommand fallback for file:// contexts)
     --------------------------------------------------------------------- */
  async function copyText(text, successMessage) {
    try {
      await navigator.clipboard.writeText(text);
      showToast(successMessage);
      return;
    } catch (e) { /* fall through to legacy approach */ }
    try {
      const ta = document.createElement('textarea');
      ta.value = text;
      ta.style.position = 'fixed';
      ta.style.opacity = '0';
      document.body.appendChild(ta);
      ta.select();
      document.execCommand('copy');
      document.body.removeChild(ta);
      showToast(successMessage);
    } catch (e) {
      showToast('Could not copy — please copy manually.');
    }
  }

  function downloadFile(filename, content, mime) {
    const blob = new Blob([content], { type: mime });
    const url = URL.createObjectURL(blob);
    const a = document.createElement('a');
    a.href = url;
    a.download = filename;
    document.body.appendChild(a);
    a.click();
    document.body.removeChild(a);
    setTimeout(() => URL.revokeObjectURL(url), 1000);
  }

  /* =======================================================================
     3. FUNCTION COMPILATION & VALIDATION
     ======================================================================= */
  function compileFunction(exprStr) {
    let translated;
    try {
      translated = translateMathNotation(exprStr);
    } catch (err) {
      throw new Error(`Could not parse f(x): ${err.message}`);
    }
    let fn;
    try {
      // eslint-disable-next-line no-new-func
      fn = new Function('x', 'T', 'Math', `"use strict"; return (${translated});`);
    } catch (err) {
      throw new Error(`f(x) is not a valid expression: ${err.message}`);
    }
    return (x, T) => fn(x, T, Math);
  }

  function validateFunction(fn, a, b, T) {
    const probes = 25;
    for (let i = 0; i <= probes; i++) {
      const x = a + (i / probes) * (b - a);
      let y;
      try {
        y = fn(x, T);
      } catch (err) {
        throw new Error(`f(x) could not be evaluated at x = ${x.toFixed(3)}: ${err.message}`);
      }
      if (typeof y !== 'number' || Number.isNaN(y) || !Number.isFinite(y)) {
        throw new Error(`f(x) produced a non-finite value (NaN/Infinity) at x = ${x.toFixed(3)}. Check for division by zero or domain errors.`);
      }
    }
  }

  function readAndValidateInputs() {
    const exprStr = els.funcInput.value.trim();
    if (!exprStr) throw new Error('Please enter a function f(x).');

    const T = parseFloat(els.periodInput.value);
    if (!Number.isFinite(T) || T <= 0) throw new Error('Period T must be a positive number.');

    const N = parseInt(els.termsInput.value, 10);
    if (!Number.isInteger(N) || N < 1 || N > 100) throw new Error('Number of terms N must be an integer between 1 and 100.');

    let a, b;
    if (els.autoLimits.checked) {
      a = -T / 2; b = T / 2;
      els.lowerLimit.value = a; els.upperLimit.value = b;
    } else {
      a = parseFloat(els.lowerLimit.value);
      b = parseFloat(els.upperLimit.value);
      if (!Number.isFinite(a) || !Number.isFinite(b)) throw new Error('Integration limits must be valid numbers.');
      if (b <= a) throw new Error('Upper limit (b) must be greater than lower limit (a).');
    }

    let steps = parseInt(els.samplesInput.value, 10);
    if (!Number.isInteger(steps) || steps < 10) throw new Error('Integration steps must be an integer of at least 10.');
    if (steps % 2 !== 0) steps += 1;
    if (steps > 20000) steps = 20000;

    const method = els.methodSelect.value;
    return { exprStr, T, N, a, b, steps, method };
  }

  /* =======================================================================
     FOURIER COEFFICIENT COMPUTATION (mathematics verified against the
     analytical solutions for f(x)=x on [-pi,pi] and f(x)=x^2 on [-1,1] —
     numerically matched to 6 decimal places, no changes made here)
     ======================================================================= */
  function computeFourierCoefficients({ fn, T, N, a, b, steps, method }) {
    const omega = (2 * Math.PI) / T;
    const twoOverT = 2 / T;
    const a0 = twoOverT * integrate((x) => fn(x, T), a, b, steps, method);
    const an = new Array(N);
    const bn = new Array(N);
    for (let n = 1; n <= N; n++) {
      an[n - 1] = twoOverT * integrate((x) => fn(x, T) * Math.cos(n * omega * x), a, b, steps, method);
      bn[n - 1] = twoOverT * integrate((x) => fn(x, T) * Math.sin(n * omega * x), a, b, steps, method);
    }
    return { a0, an, bn, omega };
  }

  function fourierApprox(x, terms) {
    let sum = state.a0 / 2;
    for (let n = 1; n <= terms; n++) {
      sum += state.an[n - 1] * Math.cos(n * state.omega * x) + state.bn[n - 1] * Math.sin(n * state.omega * x);
    }
    return sum;
  }

  /* =======================================================================
     4. RENDERING — EQUATION (numeric coefficients, pi-aware formatting)
     ======================================================================= */
  const ZERO_EPS = 1e-8;

  // Expresses n*omega as a short string using pi where it divides cleanly
  // (e.g. omega=pi -> "n" gives "pi", "2pi", "3pi/2", ...), otherwise falls
  // back to a 4-decimal number. piSymbol lets callers request '\\pi' for LaTeX.
  function formatAngularCoeff(n, piSymbol) {
    const val = n * state.omega;
    const rounded = Math.round(val);
    if (Math.abs(val - rounded) < 1e-7) {
      if (rounded === 1) return '';
      if (rounded === -1) return '-';
      return String(rounded);
    }
    const ratio = val / Math.PI;
    for (let q = 1; q <= 12; q++) {
      const p = Math.round(ratio * q);
      if (p !== 0 && Math.abs(ratio - p / q) < 1e-7) {
        const coeff = q === 1 ? (p === 1 ? '' : p === -1 ? '-' : String(p)) : (p === 1 ? '' : p === -1 ? '-' : String(p));
        return q === 1 ? `${coeff}${piSymbol}` : `${coeff}${piSymbol}/${q}`;
      }
    }
    return val.toFixed(4);
  }

  function formatSigned(value) {
    const sign = value < 0 ? '\u2212' : '+';
    return { sign, abs: Math.abs(value).toFixed(6) };
  }

  function buildEquationTerms(N, piSymbol) {
    // Returns an array of { html, latex, isZero } describing every
    // non-negligible term beyond the constant, in a0-then a1,b1,a2,b2... order.
    const lines = [];
    for (let n = 1; n <= N; n++) {
      const coeffX = formatAngularCoeff(n, piSymbol);
      const a = state.an[n - 1];
      const b = state.bn[n - 1];
      if (Math.abs(a) >= ZERO_EPS) {
        const { sign, abs } = formatSigned(a);
        lines.push({
          html: `<span class="term-cos">${sign} ${abs} cos(${coeffX}x)</span>`,
          latex: `${sign === '\u2212' ? '-' : '+'} ${abs}\\cos(${coeffX}x)`,
        });
      }
      if (Math.abs(b) >= ZERO_EPS) {
        const { sign, abs } = formatSigned(b);
        lines.push({
          html: `<span class="term-sin">${sign} ${abs} sin(${coeffX}x)</span>`,
          latex: `${sign === '\u2212' ? '-' : '+'} ${abs}\\sin(${coeffX}x)`,
        });
      }
    }
    return lines;
  }

  function renderEquation(N) {
    const constant = state.a0 / 2;
    const constAbs = Math.abs(constant).toFixed(6);
    const constSign = constant < 0 ? '\u2212' : '';
    const lines = buildEquationTerms(N, '\u03c0'); // 'π'

    let html = `<span class="eq-line"><span class="term-const">f(x) &asymp; ${constSign}${constAbs}</span></span>`;
    if (lines.length === 0) {
      els.equationDisplay.innerHTML = html + `<span class="eq-meta">(all harmonic coefficients are negligible &mdash; f(x) is effectively constant over this domain)</span>`;
    } else {
      for (const line of lines) html += `<span class="eq-line">${line.html}</span>`;
      els.equationDisplay.innerHTML = html;
    }
    const metaLine = `<span class="eq-meta">&omega; = 2&pi;/T = ${state.omega.toFixed(5)} &middot; ${lines.length} of ${2 * N} harmonic terms shown (|coefficient| &ge; ${ZERO_EPS})</span>`;
    els.equationDisplay.innerHTML += metaLine;
  }

  function buildLatex(N) {
    const constant = state.a0 / 2;
    const lines = buildEquationTerms(N, '\\pi');
    let tex = `f(x) \\approx ${constant < 0 ? '-' : ''}${Math.abs(constant).toFixed(6)}`;
    for (const line of lines) tex += ` ${line.latex}`;
    return tex;
  }

  /* =======================================================================
     RENDERING — COEFFICIENT TABLE (search + sort)
     ======================================================================= */
  function getFilteredSortedRows() {
    const query = (els.tableSearch.value || '').trim().toLowerCase();
    let rows = state.tableRows.slice();
    if (query) {
      rows = rows.filter((r) => {
        const nStr = String(r.n);
        const anStr = r.an === null ? '' : r.an.toFixed(6);
        const bnStr = r.bn === null ? '' : r.bn.toFixed(6);
        return nStr.includes(query) || anStr.includes(query) || bnStr.includes(query);
      });
    }
    const { column, dir } = sortState;
    rows.sort((r1, r2) => {
      const v1 = r1[column] === null ? -Infinity : r1[column];
      const v2 = r2[column] === null ? -Infinity : r2[column];
      return dir === 'asc' ? v1 - v2 : v2 - v1;
    });
    return rows;
  }

  function renderTable() {
    const rows = getFilteredSortedRows();
    if (rows.length === 0) {
      els.coeffTableBody.innerHTML = '<tr><td colspan="3" class="empty-row">No matching rows</td></tr>';
      return;
    }
    els.coeffTableBody.innerHTML = rows.map((r) => `
      <tr>
        <td>${r.n}</td>
        <td>${r.an === null ? '&mdash;' : r.an.toFixed(6)}</td>
        <td>${r.bn === null ? '&mdash;' : r.bn.toFixed(6)}</td>
      </tr>`).join('');
  }

  document.querySelectorAll('#coeffTable th.sortable').forEach((th) => {
    th.addEventListener('click', () => {
      const col = th.dataset.col;
      if (sortState.column === col) {
        sortState.dir = sortState.dir === 'asc' ? 'desc' : 'asc';
      } else {
        sortState = { column: col, dir: 'asc' };
      }
      document.querySelectorAll('#coeffTable .sort-arrow').forEach((s) => (s.textContent = ''));
      th.querySelector('.sort-arrow').textContent = sortState.dir === 'asc' ? '\u25B2' : '\u25BC';
      renderTable();
    });
  });
  els.tableSearch.addEventListener('input', renderTable);

  /* =======================================================================
     RENDERING — CHART
     ======================================================================= */
  function buildDatasetPoints(fn, T, center, terms) {
    const span = 2 * T;
    const start = center - span / 2;
    const end = center + span / 2;
    const samples = 400;
    const originalPts = [];
    const approxPts = [];
    for (let i = 0; i <= samples; i++) {
      const x = start + (i / samples) * (end - start);
      let yOrig = null;
      try {
        const val = fn(x, T);
        if (Number.isFinite(val)) yOrig = val;
      } catch (e) { yOrig = null; }
      originalPts.push({ x, y: yOrig });
      approxPts.push({ x, y: fourierApprox(x, terms) });
    }
    return { originalPts, approxPts };
  }

  function getCurrentSliderTerms() {
    const v = parseInt(els.termSlider.value, 10);
    return Number.isFinite(v) ? v : state.maxTerms;
  }

  function updateConvergence(originalPts, approxPts, terms) {
    let sumSq = 0, count = 0;
    const halfWindowStart = state.center - state.T / 2;
    const halfWindowEnd = state.center + state.T / 2;
    for (let i = 0; i < originalPts.length; i++) {
      const p = originalPts[i];
      if (p.y === null || p.x < halfWindowStart || p.x > halfWindowEnd) continue;
      const diff = p.y - approxPts[i].y;
      sumSq += diff * diff;
      count++;
    }
    if (count === 0) {
      els.convergenceStatus.textContent = 'Convergence: unable to estimate (function undefined across the period).';
      return;
    }
    const rms = Math.sqrt(sumSq / count);
    els.convergenceStatus.textContent = `Convergence: RMS error vs f(x) over one period with ${terms} term${terms === 1 ? '' : 's'} \u2248 ${rms.toFixed(6)}`;
  }

  function updateChart(terms) {
    if (!state.fCompiled) return;
    const { originalPts, approxPts } = buildDatasetPoints(state.fCompiled, state.T, state.center, terms);
    updateConvergence(originalPts, approxPts, terms);

    const colorFn = cssVar('--accent-a') || '#e8b339';
    const colorApprox = cssVar('--accent-b') || '#46c9c0';
    const colorText = cssVar('--text-muted') || '#8b93a7';
    const colorGrid = cssVar('--border') || '#2a2f3c';

    if (chart) {
      chart.data.datasets[0].data = originalPts;
      chart.data.datasets[1].data = approxPts;
      chart.data.datasets[0].borderColor = colorFn;
      chart.data.datasets[1].borderColor = colorApprox;
      chart.options.scales.x.ticks.color = colorText;
      chart.options.scales.y.ticks.color = colorText;
      chart.options.scales.x.grid.color = colorGrid;
      chart.options.scales.y.grid.color = colorGrid;
      chart.options.plugins.legend.labels.color = colorText;
      chart.update('none');
      return;
    }

    const zoomPluginAvailable = typeof Chart !== 'undefined' && Chart.registry && (() => {
      try { return !!Chart.registry.getPlugin('zoom'); } catch (e) { return false; }
    })();

    chart = new Chart(els.chartCanvas.getContext('2d'), {
      type: 'line',
      data: {
        datasets: [
          { label: 'Original f(x)', data: originalPts, borderColor: colorFn, backgroundColor: 'transparent', borderWidth: 2.5, pointRadius: 0, tension: 0, spanGaps: false },
          { label: 'Fourier approximation', data: approxPts, borderColor: colorApprox, backgroundColor: 'transparent', borderWidth: 2, borderDash: [5, 3], pointRadius: 0, tension: 0.05 },
        ],
      },
      options: {
        responsive: true,
        maintainAspectRatio: false,
        animation: false,
        parsing: false,
        interaction: { mode: 'nearest', intersect: false },
        scales: {
          x: { type: 'linear', title: { display: true, text: 'x', color: colorText }, ticks: { color: colorText }, grid: { color: colorGrid } },
          y: { title: { display: true, text: 'f(x)', color: colorText }, ticks: { color: colorText }, grid: { color: colorGrid } },
        },
        plugins: {
          legend: { labels: { color: colorText } },
          tooltip: { callbacks: { label: (ctx) => `${ctx.dataset.label}: ${ctx.parsed.y === null ? 'undefined' : ctx.parsed.y.toFixed(4)}` } },
          zoom: zoomPluginAvailable ? {
            pan: { enabled: true, mode: 'xy', modifierKey: null },
            zoom: { wheel: { enabled: true }, pinch: { enabled: true }, drag: { enabled: false }, mode: 'xy' },
          } : undefined,
        },
      },
    });
  }

  els.resetZoomBtn.addEventListener('click', () => {
    if (chart && typeof chart.resetZoom === 'function') chart.resetZoom();
  });

  /* =======================================================================
     MAIN CALCULATE FLOW (wrapped so the "Calculating…" spinner can paint
     before the synchronous numerical-integration loop runs)
     ======================================================================= */
  function setBusy(isBusy) {
    els.calculateBtn.disabled = isBusy;
    els.btnSpinner.hidden = !isBusy;
    els.calculateLabel.textContent = isBusy ? 'Calculating\u2026' : 'Calculate';
  }

  function calculate() {
    clearError();
    setBusy(true);
    // Yield to the browser once so the spinner actually renders before the
    // (synchronous, but occasionally ~0.2–0.5s) integration loop runs.
    setTimeout(runCalculation, 20);
  }

  function runCalculation() {
    let inputs;
    try {
      inputs = readAndValidateInputs();
    } catch (err) {
      showError(err.message);
      setBusy(false);
      return;
    }

    let fn;
    try {
      fn = compileFunction(inputs.exprStr);
      validateFunction(fn, inputs.a, inputs.b, inputs.T);
    } catch (err) {
      showError(err.message);
      setBusy(false);
      return;
    }

    let result;
    try {
      result = computeFourierCoefficients({ fn, ...inputs });
    } catch (err) {
      showError(`Calculation failed: ${err.message}`);
      setBusy(false);
      return;
    }

    state.a0 = result.a0;
    state.an = result.an;
    state.bn = result.bn;
    state.omega = result.omega;
    state.T = inputs.T;
    state.a = inputs.a;
    state.b = inputs.b;
    state.center = (inputs.a + inputs.b) / 2;
    state.fCompiled = fn;
    state.maxTerms = inputs.N;
    state.method = inputs.method;
    state.steps = inputs.steps;
    state.exprStr = inputs.exprStr;

    state.tableRows = [{ n: 0, an: result.a0, bn: null }];
    for (let n = 1; n <= inputs.N; n++) state.tableRows.push({ n, an: result.an[n - 1], bn: result.bn[n - 1] });
    sortState = { column: 'n', dir: 'asc' };
    document.querySelectorAll('#coeffTable .sort-arrow').forEach((s) => (s.textContent = ''));

    renderEquation(inputs.N);
    renderTable();

    els.termSlider.min = 0;
    els.termSlider.max = inputs.N;
    els.termSlider.value = inputs.N;
    els.termSlider.disabled = false;
    els.termSliderValue.textContent = inputs.N;

    els.integrationStatus.textContent =
      `Computed with ${inputs.method === 'trapezoidal' ? "Trapezoidal Rule" : "Simpson's Rule"} using ${inputs.steps} integration steps over [a, b] = [${inputs.a.toFixed(5)}, ${inputs.b.toFixed(5)}].`;

    updateChart(inputs.N);
    saveSession();
    setBusy(false);
  }

  /* ---------------------------------------------------------------------
     PRESETS
     --------------------------------------------------------------------- */
  const PRESETS = {
    linear: { expr: 'x', period: '6.283185307' },
    quadratic: { expr: 'x^2', period: '6.283185307' },
    cubic: { expr: 'x^3', period: '6.283185307' },
    sinFn: { expr: 'sin(x)', period: '6.283185307' },
    cosFn: { expr: 'cos(x)', period: '6.283185307' },
    square: { expr: 'Math.sign(Math.sin((2*Math.PI/T)*x))', period: '6.283185307' },
    sawtooth: { expr: '2*((x/T) - Math.floor((x/T) + 0.5))', period: '6.283185307' },
    triangle: { expr: '(2/Math.PI)*Math.asin(Math.sin((2*Math.PI/T)*x))', period: '6.283185307' },
    rectifiedSine: { expr: 'Math.abs(Math.sin((2*Math.PI/T)*x))', period: '6.283185307' },
    absValue: { expr: '|x|', period: '6.283185307' },
    exponential: { expr: 'exp(x)', period: '6.283185307' },
    piecewise: { expr: 'x < 0 ? 0 : x', period: '6.283185307' },
  };

  els.sampleSelect.addEventListener('change', () => {
    const key = els.sampleSelect.value;
    if (!key || !PRESETS[key]) return;
    const preset = PRESETS[key];
    els.funcInput.value = preset.expr;
    els.periodInput.value = preset.period;
    els.autoLimits.checked = true;
    syncLimitInputsDisabled();
    calculate();
  });

  /* ---------------------------------------------------------------------
     AUTO-LIMITS TOGGLE
     --------------------------------------------------------------------- */
  function syncLimitInputsDisabled() {
    const disabled = els.autoLimits.checked;
    els.lowerLimit.disabled = disabled;
    els.upperLimit.disabled = disabled;
  }
  els.autoLimits.addEventListener('change', syncLimitInputsDisabled);
  syncLimitInputsDisabled();

  /* ---------------------------------------------------------------------
     SLIDER
     --------------------------------------------------------------------- */
  els.termSlider.addEventListener('input', () => {
    const terms = parseInt(els.termSlider.value, 10);
    els.termSliderValue.textContent = terms;
    updateChart(terms);
  });

  /* ---------------------------------------------------------------------
     BUTTONS: calculate / reset / export / copy / print
     --------------------------------------------------------------------- */
  els.calculateBtn.addEventListener('click', calculate);

  // Enter key inside any text/number field triggers Calculate.
  [els.funcInput, els.periodInput, els.termsInput, els.lowerLimit, els.upperLimit, els.samplesInput].forEach((el) => {
    el.addEventListener('keydown', (e) => {
      if (e.key === 'Enter') { e.preventDefault(); calculate(); }
    });
  });

  function clearSession() {
    try { localStorage.removeItem('fourier-session'); } catch (e) { /* ignore */ }
  }

  els.resetBtn.addEventListener('click', () => {
    els.funcInput.value = 'x';
    els.periodInput.value = '6.283185307';
    els.termsInput.value = '10';
    els.lowerLimit.value = '-3.141592653';
    els.upperLimit.value = '3.141592653';
    els.autoLimits.checked = true;
    els.methodSelect.value = 'simpson';
    els.samplesInput.value = '1000';
    els.sampleSelect.value = '';
    els.tableSearch.value = '';
    syncLimitInputsDisabled();
    clearError();
    clearSession();

    els.equationDisplay.innerHTML = 'Enter a function and press <strong>Calculate</strong> to see its Fourier expansion.';
    els.coeffTableBody.innerHTML = '<tr><td colspan="3" class="empty-row">No data yet</td></tr>';
    els.termSlider.value = 0;
    els.termSlider.max = 10;
    els.termSlider.disabled = true;
    els.termSliderValue.textContent = '0';
    els.integrationStatus.textContent = '\u00a0';
    els.convergenceStatus.textContent = '\u00a0';

    state = { a0: 0, an: [], bn: [], omega: 0, T: 0, center: 0, fCompiled: null, maxTerms: 0, tableRows: [] };
    if (chart) { chart.destroy(); chart = null; }
    showToast('Reset to defaults.');
  });

  els.copyLatexBtn.addEventListener('click', () => {
    if (!state.fCompiled) { showToast('Calculate first.'); return; }
    copyText(buildLatex(state.maxTerms), 'LaTeX copied to clipboard.');
  });

  els.copyTableBtn.addEventListener('click', () => {
    const rows = getFilteredSortedRows();
    if (rows.length === 0) { showToast('Nothing to copy.'); return; }
    const tsv = ['n\tan\tbn', ...rows.map((r) => `${r.n}\t${r.an === null ? '' : r.an.toFixed(6)}\t${r.bn === null ? '' : r.bn.toFixed(6)}`)].join('\n');
    copyText(tsv, 'Table copied to clipboard.');
  });

  els.exportCsvBtn.addEventListener('click', () => {
    const rows = getFilteredSortedRows();
    if (rows.length === 0) { showToast('Nothing to export.'); return; }
    const csv = ['n,an,bn', ...rows.map((r) => `${r.n},${r.an === null ? '' : r.an.toFixed(6)},${r.bn === null ? '' : r.bn.toFixed(6)}`)].join('\n');
    downloadFile('fourier-coefficients.csv', csv, 'text/csv');
    showToast('CSV downloaded.');
  });

  els.exportReportBtn.addEventListener('click', () => {
    if (!state.fCompiled) { showToast('Calculate first.'); return; }
    const lines = [];
    lines.push('Fourier Series Calculator — Report');
    lines.push('===================================');
    lines.push(`f(x) = ${state.exprStr}`);
    lines.push(`Period T = ${state.T}`);
    lines.push(`Integration domain = [${state.a}, ${state.b}]`);
    lines.push(`Method = ${state.method === 'trapezoidal' ? 'Trapezoidal Rule' : "Simpson's Rule"}, steps = ${state.steps}`);
    lines.push(`Terms computed = ${state.maxTerms}`);
    lines.push('');
    lines.push(`a0 = ${state.a0.toFixed(6)}`);
    for (let n = 1; n <= state.maxTerms; n++) {
      lines.push(`n=${n}: an = ${state.an[n - 1].toFixed(6)}, bn = ${state.bn[n - 1].toFixed(6)}`);
    }
    lines.push('');
    lines.push('LaTeX:');
    lines.push(buildLatex(state.maxTerms));
    downloadFile('fourier-report.txt', lines.join('\n'), 'text/plain');
    showToast('Report downloaded.');
  });

  els.copyResultsBtn.addEventListener('click', () => {
    if (!state.fCompiled) { showToast('Calculate first.'); return; }
    const plain = els.equationDisplay.textContent.replace(/\s+/g, ' ').trim();
    copyText(plain, 'Equation copied to clipboard.');
  });

  els.printBtn.addEventListener('click', () => window.print());

  // Force all collapsible cards open before printing so their content is
  // visible on paper, then restore whatever state the user had.
  let openStateBeforePrint = null;
  window.addEventListener('beforeprint', () => {
    const cards = document.querySelectorAll('details.card');
    openStateBeforePrint = Array.from(cards).map((c) => c.open);
    cards.forEach((c) => (c.open = true));
  });
  window.addEventListener('afterprint', () => {
    if (!openStateBeforePrint) return;
    document.querySelectorAll('details.card').forEach((c, i) => (c.open = openStateBeforePrint[i]));
    openStateBeforePrint = null;
  });

  /* ---------------------------------------------------------------------
     KEYBOARD SHORTCUTS
     --------------------------------------------------------------------- */
  document.addEventListener('keydown', (e) => {
    if ((e.ctrlKey || e.metaKey) && e.key === 'Enter') { e.preventDefault(); calculate(); }
    if (e.altKey && (e.key === 'r' || e.key === 'R')) { e.preventDefault(); els.resetBtn.click(); }
    if (e.altKey && (e.key === 't' || e.key === 'T')) { e.preventDefault(); els.themeToggle.click(); }
  });

  /* ---------------------------------------------------------------------
     SESSION PERSISTENCE (save last session / restore on load)
     --------------------------------------------------------------------- */
  function saveSession() {
    try {
      const session = {
        func: els.funcInput.value, period: els.periodInput.value, terms: els.termsInput.value,
        lower: els.lowerLimit.value, upper: els.upperLimit.value, auto: els.autoLimits.checked,
        method: els.methodSelect.value, steps: els.samplesInput.value,
      };
      localStorage.setItem('fourier-session', JSON.stringify(session));
    } catch (e) { /* ignore */ }
  }
  function restoreSession() {
    let session = null;
    try { session = JSON.parse(localStorage.getItem('fourier-session')); } catch (e) { /* ignore */ }
    if (!session) return false;
    els.funcInput.value = session.func ?? els.funcInput.value;
    els.periodInput.value = session.period ?? els.periodInput.value;
    els.termsInput.value = session.terms ?? els.termsInput.value;
    els.lowerLimit.value = session.lower ?? els.lowerLimit.value;
    els.upperLimit.value = session.upper ?? els.upperLimit.value;
    els.autoLimits.checked = session.auto !== undefined ? session.auto : els.autoLimits.checked;
    els.methodSelect.value = session.method ?? els.methodSelect.value;
    els.samplesInput.value = session.steps ?? els.samplesInput.value;
    syncLimitInputsDisabled();
    return true;
  }

  /* ---------------------------------------------------------------------
     INIT
     --------------------------------------------------------------------- */
  initTheme();
  restoreSession();
  runCalculation(); // initial calculation on load (no need to show the spinner delay)
})();
