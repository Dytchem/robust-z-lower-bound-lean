"""Emit the figures and the appendix listing for the numerics section.

Inputs  : num_results.json (written by verify_num.py)
Outputs : fignum_num.pdf, appendix_seqs_num.tex
"""
import json
import math
import os

import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

plt.rcParams.update({'pdf.fonttype': 42, 'ps.fonttype': 42, 'font.size': 8, 'font.family': 'serif', 'axes.linewidth': 0.6,
                     'xtick.major.width': 0.6, 'ytick.major.width': 0.6,
                     'mathtext.fontset': 'cm', 'legend.frameon': False})
HERE = os.path.dirname(os.path.abspath(__file__))
D = json.load(open(os.path.join(HERE, 'num_results.json')))
N = np.array([d['N'] for d in D], float)
T = np.array([d['T'] for d in D], float)
TN = T / N


def figure():
    fig, ax = plt.subplots(1, 3, figsize=(7.4, 2.4))
    ticks = np.arange(2, 13, 2)
    a = ax[0]
    a.plot(N, T, 'o-', ms=3.2, lw=1.1, color='C0', label=r'T from local search')
    a.plot(N, (2 * N + 1) * np.pi, '--', lw=1.0, color='C3', label=r'equiangular')
    a.plot(N, 4 * N, ':', lw=1.2, color='C2', label=r'coefficient-4 reference')
    m = N <= 8
    p = np.polyfit(N[m], T[m], 1)
    a.plot(N, np.polyval(p, N), '-', lw=0.8, color='0.55',
           label=r'fit $5.26N+2.81$')
    a.set_xticks(ticks); a.set_yticks(np.arange(0, 81, 20))
    a.set_xlim(0, 12.6); a.set_ylim(0, 80)
    a.set_ylabel(r'$Z$ time $T$')
    a.legend(fontsize=6.0, loc='upper left')
    a.set_title(r'(a) cost', fontsize=8)

    b = ax[1]
    b.plot(N, TN, 'o-', ms=3.2, lw=1.1, color='C0')
    b.axhline(2 * np.pi, ls='--', lw=1.0, color='C3')
    b.axhline(4.0, ls=':', lw=1.2, color='C2')
    b.set_xticks(ticks); b.set_yticks(np.arange(4, 8.5, 1))
    b.set_xlim(0, 12.6); b.set_ylim(3.7, 8.5)
    b.set_ylabel(r'$T_{\mathrm{num}}(N,\pi)/N$')
    b.annotate(r'$2\pi=6.28$', (0.8, 6.45), fontsize=6.5, color='C3')
    b.annotate(r'$4$', (0.8, 4.15), fontsize=6.5, color='C2')
    b.annotate(r'$5.62$', (7.1, 5.36), fontsize=6.5, color='C0')
    b.set_title(r'(b) coefficient', fontsize=8)

    c = ax[2]
    emin = {1: 0.1, 3: 0.1, 6: 0.1, 12: 0.2}     # stop where delta reaches the round-off floor
    for d in D:
        if d['N'] in emin:
            k = int(np.sum(np.array(d['eps']) > emin[d['N']] - 1e-12))
            c.loglog(d['eps'][:k], d['delta'][:k], 'o-', ms=2.6, lw=1.0,
                     label=r'$N=%d$, slope $%.1f$' % (d['N'], d['ploc']))
    c.loglog(np.array([0.1, 0.5]), 0.53 * np.array([0.1, 0.5]) ** 2, 'k--', lw=0.8,
             label=r'slope $2$')
    c.set_xticks([0.1, 0.2, 0.5]); c.set_xticklabels(['0.1', '0.2', '0.5'])
    c.set_yticks([1e-6, 1e-4, 1e-2, 1e0])
    c.set_xlim(0.095, 0.56); c.set_ylim(3e-7, 1.5)
    c.minorticks_off()
    c.set_xlabel(r'error $\varepsilon$'); c.set_ylabel(r'deviation $\delta(\varepsilon)$')
    c.legend(fontsize=5.8, loc='lower left', handlelength=1.5,
             borderaxespad=0.25, labelspacing=0.22)
    c.set_title(r'(c) order of robustness', fontsize=8)
    for x in ax:
        x.grid(alpha=0.18, lw=0.4, which='both')
        x.tick_params(labelsize=7)
    fig.tight_layout(pad=0.35)
    fig.savefig(os.path.join(HERE, 'fignum_num.pdf'))
    print('wrote fignum_num.pdf  (fit %.3f N %+.3f over N<=8)' % (p[0], p[1]))


DEC = 12          # decimals of the printed angles, in units of pi
CHUNK = 5         # printed numbers per line


def appendix():
    import verify_num as V          # same model, same conventions
    worst_nom = worst_rho = 0.0
    out = [r'\begin{flushleft}\footnotesize\ttfamily']
    for d in D:
        N, L, T_ = d['N'], d['L'], d['T']
        out.append(r'\vspace{3pt}\par\noindent\textbf{$N=%d$}\ ($L=%d$, $T=%.4f$, '
                   r'$T/N=%.2f$):' % (N, L, T_, T_ / N))
        # the printed lists, rounded to DEC decimals of pi, are what the reader
        # can type in; the round trip below is checked, not assumed
        th = np.round(np.array(d['theta']) / np.pi, DEC) * np.pi
        al = np.round(np.array(d['alpha']) / np.pi, DEC) * np.pi
        P = V.prop(th, al, 0.0)
        nom = min(V.opnorm(P - V.target()), V.opnorm(P + V.target()))
        tau = float(th.sum()) / 2
        J = V.jets(th, al, N)
        rho = max(math.factorial(k) * V.opnorm(J[k]) / tau ** k
                  for k in range(1, N + 1))
        worst_nom, worst_rho = max(worst_nom, nom), max(worst_rho, rho)
        for lab, x in ((r'\theta', d['theta']), (r'\alpha', d['alpha'])):
            out.append(r'\par\noindent$%s/\pi$ (time order):' % lab)
            s = [f'{v / np.pi:+.{DEC}f}' for v in x]
            out.append(' \\\\\n'.join(', '.join(s[i:i + CHUNK])
                                      for i in range(0, len(s), CHUNK)))
    out.append(r'\end{flushleft}')
    open(os.path.join(HERE, 'appendix_seqs_num.tex'), 'w').write('\n'.join(out) + '\n')
    print('wrote appendix_seqs_num.tex  (round trip from the printed %d decimals: '
          'max nom %.1e, max rho %.1e)' % (DEC, worst_nom, worst_rho))


GAMMA = 1e4 / (2 * np.pi * 500e6)   # gamma/omega for gamma = 0.01 MHz, Vbar/2pi = 500 MHz
EPSTRY = 0.12                        # deltaV/Vbar estimate of the Rydberg protocol


def physics():
    """The coherent-versus-incoherent balance at the parameters of the Rydberg
    protocol: coherent error from the tabulated sequences at a fixed eps, against
    an incoherent error proportional to the exposure time T."""
    import verify_num as V

    rows = []
    for d in D[:8]:
        th = np.array(d['theta']); al = np.array(d['alpha'])
        U = V.prop(th, al, EPSTRY)
        ov = abs(float(np.real(np.trace(U.conj().T @ V.target())))) / 2
        de = math.acos(min(1.0, max(-1.0, ov)))
        rows.append((d['N'], d['T'], de, math.sin(de / 2) ** 2, d['T'] * GAMMA))
    best = min(rows, key=lambda r: r[3] + r[4])
    print('coherent/incoherent balance: N* = %d (total %.2e)' % (best[0], best[3] + best[4]))

    fig, ax = plt.subplots(1, 2, figsize=(7.4, 2.5))
    Ns = np.array([r[0] for r in rows])
    a = ax[0]
    a.semilogy(Ns, [r[3] for r in rows], 'o-', ms=3, lw=1.1, color='C0',
               label=r'coherent, $1-F_{\mathrm{coh}}$')
    a.semilogy(Ns, [r[4] for r in rows], 's--', ms=3, lw=1.1, color='C3',
               label=r'incoherent, $\gamma T/\omega$')
    a.semilogy(Ns, [r[3] + r[4] for r in rows], '^-', ms=3.2, lw=1.3, color='k', label='total')
    a.plot([best[0]], [best[3] + best[4]], marker='*', ms=9, color='C2', zorder=5,
           label=r'$N^\ast=%d$' % best[0])
    a.set_xticks(Ns)
    a.set_xlabel(r'robustness order $N$')
    a.set_ylabel('infidelity')
    a.set_title(r'(a) balance at $\gamma/\omega=3\times10^{-6}$, $\varepsilon=0.12$', fontsize=7.5)
    a.legend(fontsize=6, loc='lower left')

    b = ax[1]
    scales = np.logspace(0, -4, 25)
    star = []
    for sc in scales:
        star.append(min(((r[0], r[3] + r[4] * sc) for r in rows), key=lambda z: z[1])[0])
    b.semilogx(GAMMA * scales, star, 'o-', ms=3, lw=1.2, color='C0')
    b.set_xlabel(r'coherence ratio $\gamma/\omega$')
    b.set_ylabel(r'optimal order $N^\ast$')
    b.set_yticks(range(0, 9)); b.set_ylim(0.5, 8.5)
    b.set_title(r'(b) $\varepsilon=0.12$: $N^\ast$ grows logarithmically', fontsize=7.5)
    for x in ax:
        x.grid(alpha=0.18, lw=0.4, which='both'); x.tick_params(labelsize=7)
    fig.tight_layout(pad=0.35)
    fig.savefig(os.path.join(HERE, 'figphys.pdf'))
    print('wrote figphys.pdf')


if __name__ == '__main__':
    figure()
    appendix()
    physics()
