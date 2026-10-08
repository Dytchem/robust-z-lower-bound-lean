"""Independent re-verification of the numerical sequences, phi = pi, N = 1..12.

The model, written exactly as it is evaluated below.  With L = len(theta) costly
segments and alpha carrying L or L+1 free rotations, the propagator is

    U(eps) = X(a_{L+1}) X(a_L) Z((1+eps) th_L) X(a_{L-1}) Z((1+eps) th_{L-1})
             ... X(a_1) Z((1+eps) th_1)

(the outer X(a_{L+1}) is present only when alpha has L+1 entries), i.e. the
sequence of the paper read left to right,

    X(a_1) Z(th_1) X(a_2) Z(th_2) ... X(a_L) Z(th_L) X(a_{L+1}),

is applied from right to left in time.  The target is Z(pi) up to the global sign
X(2 pi) = -I, and the free rotations are exact.

The propagator is rebuilt from scratch: every factor is a scipy.linalg.expm of a
2x2 generator, with no call into the optimiser that produced the angles.  For each
stored solution:

  (a) nominal identity   U(0) = +/- Z(pi);
  (b) flatness           the Taylor coefficients c_k = [eps^k] U(eps) about
                         eps = 0, hence the derivatives
                         u_k = d^k U / d eps^k |_0 = k! c_k, for k = 1..N.
                         The coefficients are computed twice, by two independent
                         implementations that share no code: a truncated
                         convolution in double precision, and a matrix
                         series evaluated at 50 significant decimal digits with mpmath.
                         Because a general sequence has ||u_k|| of size tau^k with
                         tau = T/2 (the a priori bound of the paper), the meaningful residual is
                         the dimensionless ratio rho = max_k ||u_k|| / tau^k;
                         the residual of the stored angles themselves is ~1e-10,
                         and rho is reported against that benchmark.
  (c) order of robustness  delta(eps) ~ C eps^(N+1), from the log-log slope of the
                         operator distance delta(eps) = arccos(|<U(eps), Z(pi)>|/2)
                         over a window above the round-off floor.

All matrix norms are operator norms (largest singular value), as in the paper.

Outputs: num_results.json and num_tables.tex (the LaTeX rows of Table 2, so that
the table of the paper is generated from the verified data and cannot drift).
"""
import json
import math
import os

import numpy as np
from scipy.linalg import expm

SZ = np.array([[1.0, 0.0], [0.0, -1.0]], dtype=complex)
SX = np.array([[0.0, 1.0], [1.0, 0.0]], dtype=complex)
I2 = np.eye(2, dtype=complex)
PHI = np.pi
HERE = os.path.dirname(os.path.abspath(__file__))
SRC = os.path.join(HERE, 'solutions_largeN.json')


def ez(t):
    return expm(-0.5j * t * SZ)


def ex(a):
    return expm(-0.5j * a * SX)


def normalise(theta, alpha, extra=1):
    """The published pair: the surplus angles merged, then reduced modulo 2 pi.

    Merging the surplus free rotations uses X(a)X(b) = X(a+b); reducing an angle
    modulo 2 pi uses X(a + 2 pi) = -X(a), which changes the propagator only by a
    global sign.  Both steps leave the sequence of the paper intact, and they put
    the printed lists in the ranges in which Appendix G states them.
    """
    th = np.asarray(theta, float)
    al = np.asarray(alpha, float)
    if extra > 1:
        al = np.concatenate([al[:len(al) - extra], [al[len(al) - extra:].sum()]])
    return th, np.mod(al, 2.0 * PHI)


def prop(theta, alpha, eps):
    """U(eps), as displayed in the docstring above."""
    L = len(theta)
    U = np.eye(2, dtype=complex)
    for j in range(L - 1, -1, -1):                # X(a_j) Z(th_j), innermost first
        U = U @ ex(alpha[j]) @ ez((1.0 + eps) * theta[j])
    for k in range(L, len(alpha)):                # surplus X's are the outermost
        U = ex(alpha[k]) @ U
    return U


def opnorm(M):
    """Operator norm (largest singular value) of a 2x2 matrix."""
    return float(np.linalg.norm(np.asarray(M, dtype=complex), 2))


def target(phi=PHI):
    return expm(-0.5j * phi * SZ)


def overlap(U, phi=PHI):
    """|<U, Z(phi)>|/2; the modulus removes the global sign of the two branches."""
    return abs(float(np.real(np.trace(U.conj().T @ target(phi))))) / 2.0


def dist(U, phi=PHI):
    """Operator distance to the target, measured as a rotation angle."""
    return float(np.arccos(min(1.0, max(-1.0, overlap(U, phi)))))


def sign(U, phi=PHI):
    return 1.0 if float(np.real(np.trace(U.conj().T @ target(phi)))) >= 0 else -1.0


def jets(theta, alpha, K):
    """Taylor coefficients c_k = [eps^k] U(eps), k = 0..K (double precision).

    The truncated convolution `new[m] += S[k] @ P[l]`, m = k+l, is what makes the
    higher coefficients non-trivial: a per-order rescaling of the list would leave
    every coefficient above order zero identically zero.  The order of the factors
    is the one of `prop`, and `main` asserts c_0 == U(0).
    """
    L = len(theta)
    P = [np.zeros_like(I2) for _ in range(K + 1)]
    P[0] = np.eye(2, dtype=complex)
    for j in range(L):                                  # factors, innermost first
        t = float(theta[j])
        g = -0.5j * t * SZ                              # generator of Z((1+eps) t)
        S, M, fact = [], np.eye(2, dtype=complex), 1.0
        for k in range(K + 1):                          # S_k = Z(t) g^k / k!
            if k:
                fact *= k
            S.append(ez(t) @ (M / fact))
            M = M @ g
        new = [np.zeros_like(I2) for _ in range(K + 1)]
        for k in range(K + 1):
            for l in range(K + 1 - k):
                new[k + l] = new[k + l] + S[k] @ P[l]   # left factor Z((1+eps) t)
        P = [ex(alpha[j]) @ new[k] for k in range(K + 1)]   # left factor X(a_j)
    for k in range(L, len(alpha)):                      # surplus X's are outermost
        P = [ex(alpha[k]) @ P[m] for m in range(K + 1)]
    return P


def jets_mp(theta, alpha, K, dps=50):
    """The same coefficients at 50 significant decimal digits (mpmath), sharing no code."""
    import mpmath as mp
    mp.mp.dps = dps
    eye = mp.matrix([[1, 0], [0, 1]])

    def mX(a):
        a = mp.mpf(repr(float(a)))
        c, s = mp.cos(a / 2), mp.sin(a / 2)
        return mp.matrix([[c, -1j * s], [-1j * s, c]])

    def mp_opnorm(M):
        """Operator norm of a 2x2 matrix, from the eigenvalues of M^dag M."""
        H = M.conjugate().T * M
        a, d, b = H[0, 0].real, H[1, 1].real, H[0, 1]
        tr, det = a + d, a * d - abs(b) ** 2
        disc = mp.sqrt(max(mp.mpf(0), tr * tr - 4 * det))
        return mp.sqrt((tr + disc) / 2)

    L = len(theta)
    P = [mp.matrix(2, 2) for _ in range(K + 1)]
    P[0] = eye.copy()
    for j in range(L):
        t = mp.mpf(repr(float(theta[j])))
        c, s = mp.cos(t / 2), mp.sin(t / 2)
        Zt = mp.matrix([[c - 1j * s, 0], [0, c + 1j * s]])
        g = mp.matrix([[-0.5j * t, 0], [0, 0.5j * t]])
        S, M, fact = [], eye.copy(), mp.mpf(1)
        for k in range(K + 1):
            if k:
                fact *= k
            S.append(Zt * (M / fact))
            M = M @ g
        new = [mp.matrix(2, 2) for _ in range(K + 1)]
        for k in range(K + 1):
            for l in range(K + 1 - k):
                new[k + l] = new[k + l] + S[k] @ P[l]
        P = [mX(alpha[j]) @ new[k] for k in range(K + 1)]
    for k in range(L, len(alpha)):
        P = [mX(alpha[k]) @ P[m] for m in range(K + 1)]
    return P, mp, mp_opnorm


def main():
    if not os.path.exists(SRC):
        raise SystemExit('solutions_largeN.json not found next to verify_num.py')
    eps_grid = [0.5, 0.45, 0.4, 0.35, 0.3, 0.25, 0.2, 0.15, 0.1]
    rows = sorted(json.load(open(SRC)), key=lambda r: r['N'])
    out = []
    for r in rows:
        N = int(r['N'])
        th, al = normalise(r["theta"], r["alpha"], int(r.get("extra", 1)))
        T = float(th.sum())
        tau = T / 2.0
        U0 = prop(th, al, 0.0)
        nom = opnorm(U0 - sign(U0) * target())
        # (b) flatness, evaluated twice, by two independent implementations
        P = jets(th, al, N)
        assert np.allclose(P[0], U0, rtol=0, atol=1e-13), f"jets[0] != U(0) at N={N}"
        u = np.array([math.factorial(k) * opnorm(P[k]) for k in range(N + 1)])
        Q, mp, mp_opnorm = jets_mp(th, al, N)
        assert np.allclose(np.array(Q[0].tolist()), U0, rtol=0, atol=1e-13), \
            f"mpmath jets[0] != U(0) at N={N}"
        u_mp = np.array([math.factorial(k) * float(mp_opnorm(Q[k]))
                         for k in range(N + 1)])
        # The two implementations are independent.  The reported residual is the
        # one from the 50-digit run; the double-precision convolution loses digits
        # at individual orders (it grows like tau^k before cancelling to rho*tau^k),
        # so only the reported maximum is required to agree.
        rho = float(np.max(u_mp[1:] / tau ** np.arange(1, N + 1)))
        rho_dp = float(np.max(u[1:] / tau ** np.arange(1, N + 1)))
        assert abs(rho_dp - rho) <= 1e-2 * rho, f"jets disagree at N={N}"
        # (c) the robustness law
        eps = np.array(eps_grid, float)
        delt = np.array([dist(prop(th, al, e)) for e in eps])
        sl = []
        for i in range(len(eps) - 1):
            if delt[i] > 0 and delt[i + 1] > 0:
                sl.append(float(np.log(delt[i] / delt[i + 1]) /
                                np.log(eps[i] / eps[i + 1])))
        m = delt > 5e-8
        ploc = float(np.polyfit(np.log(eps[m]), np.log(delt[m]), 1)[0]) \
            if m.sum() >= 3 else None
        out.append(dict(N=N, L=len(th), nX=len(al), T=T, T_over_N=T / N, tau=tau,
                        ratio_eq=T / (2 * N * np.pi + PHI), nom=nom, rho=rho,
                        rho_dp=rho_dp, umax=float(np.max(u[1:])),
                        umax_mp=float(np.max(u_mp[1:])), eps=eps.tolist(),
                        delta=delt.tolist(), slope=sl, ploc=ploc,
                        theta=th.tolist(), alpha=al.tolist()))
        print(f"N={N:>2} L={len(th):>3} T={T:9.5f} nom={nom:.2e} "
              f"max_k||u_k||={np.max(u_mp[1:]):.2e} rho={rho:.2e} "
              f"(dp {rho_dp:.2e}) dev(1/2)={delt[0]:.4f} "
              f"slopes={[round(s, 2) for s in sl[-3:]]} "
              f"ploc={None if ploc is None else round(ploc, 3)} (N+1={N + 1})")
    json.dump(out, open(os.path.join(HERE, 'num_results.json'), 'w'), indent=1)

    def sci(x):
        """LaTeX scientific notation, mantissa with one decimal."""
        e = math.floor(math.log10(abs(x)))
        return f"${x / 10.0 ** e:.1f}\\!\\cdot\\!10^{{{e}}}$"

    lines = []
    for d in out:
        sl = d['slope']
        lines.append(
            f"${d['N']}$ & ${d['L']}$ & ${d['T']:.4f}$ & ${d['T_over_N']:.3f}$ & "
            f"${d['ratio_eq']:.3f}$ & {sci(d['nom'])} & {sci(d['rho'])} & "
            f"{', '.join(f'{s:.2f}' for s in sl[-3:])} \\\\")
    tex = ('% generated by verify_num.py -- do not edit\n'
           '\\begin{tabular}{rrrrrrrr}\n\\toprule\n'
           '$N$ & $L$ & $T$ & $T/N$ & $T/(2N{+}1)\\pi$ & $\\lVert U_{1}\\mp Z(\\pi)\\rVert$ & '
           '$\\rho_N$ & slopes of $\\delta$ \\\\\n\\midrule\n'
           + '\n'.join(lines) + '\n\\bottomrule\n\\end{tabular}\n')
    open(os.path.join(HERE, 'num_tables.tex'), 'w').write(tex)
    print('\nwrote num_results.json and num_tables.tex')


if __name__ == '__main__':
    main()
