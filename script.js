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

function redondear(x, decimales) {
  const f = 10 ** decimales;
  return Math.round(x * f) / f;
}

// Término con signo explícito ("+ 12.5 x_0_5_0" o "- 3.2 x_1_5_0"), para armar
// expresiones lineales con coeficientes que no son todos +1.
function formatSignedTerm(coef, nombre) {
  const signo = coef < 0 ? '-' : '+';
  return `${signo} ${redondear(Math.abs(coef), 6)} ${nombre}`;
}

// Distancia promedio "natural" de cada equipo a los demás (constante: depende
// solo de la geografía, no del fixture que arme el solver).
function calcularDistanciasPromedio(distancias) {
  const n = distancias.length;
  return distancias.map((fila, i) => {
    const suma = fila.reduce((acc, d, j) => (j === i ? acc : acc + d), 0);
    return suma / (n - 1);
  });
}

function construirModeloLP(distancias, opciones) {
  const n = distancias.length;
  const rounds = n - 1; // round-robin simple, n par
  const variables = [];

  for (let i = 0; i < n; i++) {
    for (let j = 0; j < n; j++) {
      if (i === j) continue;
      for (let k = 0; k < rounds; k++) {
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

  // (5) Opcional: un partido fijo (ej. el clásico) en una fecha determinada.
  if (opciones.partidoFijo) {
    const { local, visitante, fecha } = opciones.partidoFijo;
    constraints.push(` c${cIdx++}: ${varName(local, visitante, fecha)} = 1`);
  }

  // Objetivo: para cada equipo, que la distancia total que recorre de
  // visitante esté lo más cerca posible de "su distancia promedio natural a
  // los demás equipos" multiplicada por la cantidad de partidos que le toque
  // jugar de visitante. d_m es el valor absoluto de esa desviación
  // (linealizado con las dos restricciones de siempre: d >= expr, d >= -expr).
  const avgDist = calcularDistanciasPromedio(distancias);
  const dVars = [];
  for (let m = 0; m < n; m++) {
    const terms = []; // { coef, nombre }, expresión = distTravel_m - avg_m * away_m
    for (let i = 0; i < n; i++) {
      if (i === m) continue;
      for (let k = 0; k < rounds; k++) {
        terms.push({ coef: distancias[i][m] - avgDist[m], nombre: varName(i, m, k) });
      }
    }
    const dName = `d_${m}`;
    dVars.push(dName);
    const exprMasTerms = terms.map((t) => formatSignedTerm(t.coef, t.nombre)).join(' ');
    const exprMenosTerms = terms.map((t) => formatSignedTerm(-t.coef, t.nombre)).join(' ');
    constraints.push(` c${cIdx++}: ${dName} ${exprMenosTerms} >= 0`);
    constraints.push(` c${cIdx++}: ${dName} ${exprMasTerms} >= 0`);
  }
  const objTerms = dVars.map((v) => v);

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

// Resumen por equipo: distancia total recorrida de visitante, cantidad de
// partidos de visitante, promedio real, y su promedio "natural" (geográfico).
function calcularResumenPorEquipo(partidos, distancias) {
  const n = distancias.length;
  const avgDist = calcularDistanciasPromedio(distancias);
  const resumen = Array.from({ length: n }, () => ({ totalVisitante: 0, partidosVisitante: 0 }));
  partidos.forEach((p) => {
    resumen[p.visitante].totalVisitante += distancias[p.local][p.visitante];
    resumen[p.visitante].partidosVisitante += 1;
  });
  return resumen.map((r, i) => ({
    totalVisitante: r.totalVisitante,
    partidosVisitante: r.partidosVisitante,
    promedioReal: r.partidosVisitante > 0 ? r.totalVisitante / r.partidosVisitante : 0,
    promedioNatural: avgDist[i],
  }));
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
      toggleClasico: document.getElementById('toggle-clasico'),
      selectClasicoLocal: document.getElementById('select-clasico-local'),
      btnResolver: document.getElementById('btn-resolver'),
      estadoResolucion: document.getElementById('estado-resolucion'),
      resultadoCard: document.getElementById('resultado-card'),
      resultadoResumen: document.getElementById('resultado-resumen'),
      resultadoTablero: document.getElementById('resultado-tablero'),
      resultadoEquipos: document.getElementById('resultado-equipos'),
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
      this.dom.estadoResolucion.textContent = 'Resolviendo el modelo (puede tardar hasta 45 segundos, es un problema de optimización combinatoria real)…';

      const opciones = {
        localia: this.dom.toggleLocalia.checked,
        rachas: this.dom.toggleRachas.checked,
      };
      if (this.dom.toggleClasico.checked) {
        const riverIdx = CLUBES.findIndex((c) => c.nombre === 'River');
        const bocaIdx = CLUBES.findIndex((c) => c.nombre === 'Boca');
        const localEsRiver = this.dom.selectClasicoLocal.value === 'river';
        opciones.partidoFijo = {
          local: localEsRiver ? riverIdx : bocaIdx,
          visitante: localEsRiver ? bocaIdx : riverIdx,
          fecha: 4, // Fecha 5 (0-indexada)
        };
      }
      const lp = construirModeloLP(this.distancias, opciones);

      // Se cede el hilo para que el navegador pinte el mensaje de estado antes de bloquear resolviendo.
      await new Promise((r) => setTimeout(r, 30));

      const t0 = performance.now();
      const solucion = highs.solve(lp, { output_flag: false, time_limit: 45, mip_rel_gap: 0.01 });
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
      `Desviación total del objetivo: <strong>${Math.round(solucion.ObjectiveValue).toLocaleString('es-AR')} km</strong> ` +
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

    const resumen = calcularResumenPorEquipo(partidos, this.distancias);
    let tabla = '<table class="matriz-table equipos-resumen"><thead><tr><th>Equipo</th><th>Partidos de visitante</th><th>Distancia total</th><th>Promedio real</th><th>Promedio natural</th></tr></thead><tbody>';
    resumen.forEach((r, i) => {
      tabla += `<tr>
        <th>${escapeHtml(CLUBES[i].nombre)}</th>
        <td>${r.partidosVisitante}</td>
        <td>${r.totalVisitante.toLocaleString('es-AR')} km</td>
        <td>${r.promedioReal.toFixed(0)} km</td>
        <td>${r.promedioNatural.toFixed(0)} km</td>
      </tr>`;
    });
    tabla += '</tbody></table>';
    this.dom.resultadoEquipos.innerHTML = tabla;

    this.dom.resultadoCard.hidden = false;
  }
}

function escapeHtml(str) {
  return String(str).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
}

document.addEventListener('DOMContentLoaded', () => {
  new OptimizadorApp();
});
