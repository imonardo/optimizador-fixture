'use strict';

const CLUB_COLORS = ['#1072BB', '#e5484d', '#1fa759', '#c98a06', '#8b5cf6', '#ec4899', '#01B2DB', '#f97316', '#64748b', '#14b8a6'];

// Coordenadas reales de los estadios (fuente: Wikipedia / Wikidata).
const CLUBES = [
  { nombre: 'River', lat: -34.54528, lon: -58.44972 },
  { nombre: 'Boca', lat: -34.635624, lon: -58.364967 },
  { nombre: 'Racing', lat: -34.6675, lon: -58.3686 },
  { nombre: 'Tigre', lat: -34.44944, lon: -58.54222 },
  { nombre: 'Aldosivi', lat: -38.01806, lon: -57.58222 },
  { nombre: 'Atl. Tucumán', lat: -26.8077, lon: -65.1928 },
  { nombre: 'Ind. Rivadavia', lat: -32.89058, lon: -68.8629 },
  { nombre: 'Rosario Central', lat: -32.913997, lon: -60.674567 },
  { nombre: 'Belgrano', lat: -31.4035, lon: -64.2063 },
  { nombre: 'Central Córdoba (SdE)', lat: -27.79389, lon: -64.26417 },
];

function haversine(lat1, lon1, lat2, lon2) {
  const R = 6371;
  const toRad = (d) => (d * Math.PI) / 180;
  const dLat = toRad(lat2 - lat1);
  const dLon = toRad(lon2 - lon1);
  const a =
    Math.sin(dLat / 2) ** 2 +
    Math.cos(toRad(lat1)) * Math.cos(toRad(lat2)) * Math.sin(dLon / 2) ** 2;
  return Math.round(R * 2 * Math.atan2(Math.sqrt(a), Math.sqrt(1 - a)));
}

function construirMatrizDistancias(clubes) {
  return clubes.map((a) => clubes.map((b) => (a === b ? 0 : haversine(a.lat, a.lon, b.lat, b.lon))));
}

// ============================================================
// MODELO: construcción del programa lineal entero (formato CPLEX LP)
// ============================================================

function varName(i, j, k) {
  return `x_${i}_${j}_${k}`;
}

function construirModeloLP(distancias, opciones) {
  const n = distancias.length;
  const rounds = n - 1; // round-robin simple, n par
  const variables = [];

  // Objetivo: minimizar distancia total de los partidos de visitante.
  const objTerms = [];
  for (let i = 0; i < n; i++) {
    for (let j = 0; j < n; j++) {
      if (i === j) continue;
      for (let k = 0; k < rounds; k++) {
        objTerms.push(`${distancias[i][j]} ${varName(i, j, k)}`);
        variables.push(varName(i, j, k));
      }
    }
  }

  const constraints = [];
  let cIdx = 1;

  // (1) Cada par de equipos se enfrenta exactamente una vez.
  for (let i = 0; i < n; i++) {
    for (let j = i + 1; j < n; j++) {
      const terms = [];
      for (let k = 0; k < rounds; k++) {
        terms.push(varName(i, j, k));
        terms.push(varName(j, i, k));
      }
      constraints.push(` c${cIdx++}: ${terms.join(' + ')} = 1`);
    }
  }

  // (2) Cada equipo juega exactamente un partido por fecha.
  for (let i = 0; i < n; i++) {
    for (let k = 0; k < rounds; k++) {
      const terms = [];
      for (let j = 0; j < n; j++) {
        if (j === i) continue;
        terms.push(varName(i, j, k));
        terms.push(varName(j, i, k));
      }
      constraints.push(` c${cIdx++}: ${terms.join(' + ')} = 1`);
    }
  }

  // (3) Opcional: equilibrio de localías (diferencia local/visitante <= 1).
  if (opciones.localia) {
    for (let i = 0; i < n; i++) {
      const homeTerms = [];
      const awayTerms = [];
      for (let j = 0; j < n; j++) {
        if (j === i) continue;
        for (let k = 0; k < rounds; k++) {
          homeTerms.push(varName(i, j, k));
          awayTerms.push(`- ${varName(j, i, k)}`);
        }
      }
      const expr = `${homeTerms.join(' + ')} ${awayTerms.join(' ')}`;
      constraints.push(` c${cIdx++}: ${expr} <= 1`);
      constraints.push(` c${cIdx++}: ${expr} >= -1`);
    }
  }

  // (4) Opcional: sin rachas de más de 2 partidos seguidos en la misma condición.
  if (opciones.rachas) {
    for (let i = 0; i < n; i++) {
      for (let k0 = 0; k0 <= rounds - 3; k0++) {
        const terms = [];
        for (let k = k0; k < k0 + 3; k++) {
          for (let j = 0; j < n; j++) {
            if (j === i) continue;
            terms.push(varName(i, j, k));
          }
        }
        constraints.push(` c${cIdx++}: ${terms.join(' + ')} <= 2`);
        constraints.push(` c${cIdx++}: ${terms.join(' + ')} >= 1`);
      }
    }
  }

  const boundsLines = variables.map((v) => ` ${v} <= 1`);
  const generalLines = variables.map((v) => ` ${v}`);

  return [
    'Minimize',
    ` obj: ${objTerms.join(' + ')}`,
    'Subject To',
    ...constraints,
    'Bounds',
    ...boundsLines,
    'General',
    ...generalLines,
    'End',
  ].join('\n');
}

function extraerFixture(solucion, n) {
  const rounds = n - 1;
  const partidos = []; // {fecha, local, visitante}
  for (let i = 0; i < n; i++) {
    for (let j = 0; j < n; j++) {
      if (i === j) continue;
      for (let k = 0; k < rounds; k++) {
        const columna = solucion.Columns[varName(i, j, k)];
        if (columna && Math.round(columna.Primal) === 1) {
          partidos.push({ fecha: k, local: i, visitante: j });
        }
      }
    }
  }
  return partidos;
}

// ============================================================
// APP: manejo del DOM
// ============================================================

class OptimizadorApp {
  constructor() {
    this.distancias = construirMatrizDistancias(CLUBES);
    this.dom = {
      clubesContainer: document.getElementById('clubes-container'),
      distanciasContainer: document.getElementById('distancias-container'),
      toggleLocalia: document.getElementById('toggle-localia'),
      toggleRachas: document.getElementById('toggle-rachas'),
      btnResolver: document.getElementById('btn-resolver'),
      estadoResolucion: document.getElementById('estado-resolucion'),
      resultadoCard: document.getElementById('resultado-card'),
      resultadoResumen: document.getElementById('resultado-resumen'),
      resultadoTablero: document.getElementById('resultado-tablero'),
    };
    this.highsPromise = null;
    this.init();
  }

  init() {
    this.renderClubes();
    this.renderDistancias();
    this.dom.btnResolver.addEventListener('click', () => this.onResolver());
  }

  renderClubes() {
    this.dom.clubesContainer.innerHTML = CLUBES.map(
      (c, i) => `<div class="club-chip" style="background:${CLUB_COLORS[i]}">${escapeHtml(c.nombre)}</div>`
    ).join('');
  }

  renderDistancias() {
    let html = '<table class="matriz-table"><thead><tr><th></th>';
    CLUBES.forEach((c) => { html += `<th>${escapeHtml(c.nombre)}</th>`; });
    html += '</tr></thead><tbody>';
    CLUBES.forEach((fila, i) => {
      html += `<tr><th>${escapeHtml(fila.nombre)}</th>`;
      CLUBES.forEach((col, j) => {
        html += i === j ? '<td class="cell-diagonal">—</td>' : `<td>${this.distancias[i][j]}</td>`;
      });
      html += '</tr>';
    });
    html += '</tbody></table>';
    this.dom.distanciasContainer.innerHTML = html;
  }

  async cargarHighs() {
    if (!this.highsPromise) {
      this.highsPromise = Module({
        locateFile: (file) => `https://cdn.jsdelivr.net/npm/highs@1.15.2/build/${file}`,
      });
    }
    return this.highsPromise;
  }

  async onResolver() {
    this.dom.btnResolver.disabled = true;
    this.dom.estadoResolucion.textContent = 'Cargando el solver…';
    this.dom.resultadoCard.hidden = true;

    try {
      const highs = await this.cargarHighs();
      this.dom.estadoResolucion.textContent = 'Resolviendo el modelo (puede tardar unos segundos)…';

      const opciones = {
        localia: this.dom.toggleLocalia.checked,
        rachas: this.dom.toggleRachas.checked,
      };
      const lp = construirModeloLP(this.distancias, opciones);

      // Se cede el hilo para que el navegador pinte el mensaje de estado antes de bloquear resolviendo.
      await new Promise((r) => setTimeout(r, 30));

      const t0 = performance.now();
      const solucion = highs.solve(lp, { output_flag: false, time_limit: 60 });
      const segundos = ((performance.now() - t0) / 1000).toFixed(1);

      if (solucion.Status !== 'Optimal' && !solucion.Columns) {
        this.dom.estadoResolucion.textContent = `El solver no encontró una solución (estado: ${solucion.Status}).`;
        return;
      }

      const partidos = extraerFixture(solucion, CLUBES.length);
      this.mostrarResultado(solucion, partidos, segundos);
      this.dom.estadoResolucion.textContent = '';
    } catch (err) {
      this.dom.estadoResolucion.textContent = 'Ocurrió un error al resolver. Revisá tu conexión a internet (el solver se carga desde un CDN).';
      console.error(err);
    } finally {
      this.dom.btnResolver.disabled = false;
    }
  }

  mostrarResultado(solucion, partidos, segundos) {
    const n = CLUBES.length;
    const rounds = n - 1;
    const optimo = solucion.Status === 'Optimal';

    this.dom.resultadoResumen.innerHTML =
      `Distancia total: <strong>${Math.round(solucion.ObjectiveValue).toLocaleString('es-AR')} km</strong> ` +
      `— resuelto en ${segundos}s ` +
      (optimo ? '(óptimo garantizado)' : `<span class="badge-warn">(mejor solución encontrada, estado: ${escapeHtml(solucion.Status)})</span>`);

    let html = '';
    for (let k = 0; k < rounds; k++) {
      html += `<div class="fecha-column"><div class="fecha-title">Fecha ${k + 1}</div>`;
      partidos
        .filter((p) => p.fecha === k)
        .forEach((p) => {
          const local = CLUBES[p.local].nombre;
          const visitante = CLUBES[p.visitante].nombre;
          const dist = this.distancias[p.local][p.visitante];
          html += `<div class="partido-row"><span class="local">${escapeHtml(local)}</span> vs ${escapeHtml(visitante)} <span class="dist">${dist} km</span></div>`;
        });
      html += '</div>';
    }
    this.dom.resultadoTablero.innerHTML = html;
    this.dom.resultadoCard.hidden = false;
  }
}

function escapeHtml(str) {
  return String(str).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
}

document.addEventListener('DOMContentLoaded', () => {
  new OptimizadorApp();
});
