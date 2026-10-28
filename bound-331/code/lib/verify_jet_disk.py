"""Numerical support for the determinant comparison. Source history is in the paper.

Retained function bodies are unchanged. Unused top-level functions and the
standalone historical demonstration are omitted. See ../README.md for scope.
"""
#!/usr/bin/env python3

import bisect
from decimal import Context, Decimal, ROUND_CEILING, ROUND_FLOOR
import math
import time


def sum_floor_s_tri(S: int, m_div: int) -> int:
    """
    Exact integer evaluation of sum_{s=0}^{S-1} floor(s / m_div) * (S - s) from Lemma 4.2,
    computed using only exact Python integer arithmetic (//).
    """
    if m_div > S:
        return 0
    q, r0 = divmod(S, m_div)
    return (
        (m_div * q * (q - 1) * (2 * m_div * (q + 1) + 3 * (2 * r0 - m_div + 1))) // 12
        + (q * r0 * (r0 + 1)) // 2
    )


_NA = math.nextafter
_INF = math.inf
_NINF = -math.inf
CTX_LO = Context(prec=26, rounding=ROUND_FLOOR)
CTX_HI = Context(prec=26, rounding=ROUND_CEILING)
_D0 = Decimal(0)
_D1 = Decimal(1)
_D2 = Decimal(2)
_FACT17 = Decimal(355687428096000)  # exact 17!


def _artanh_exact_dec(t_lo: Decimal, t_hi: Decimal, n_terms: int = 6):
    """
    Rigorous enclosure of ln((1+t)/(1-t)) = 2 * sum_{k>=0} t^{2k+1}/(2k+1) for 0 <= t_lo <= t <= t_hi < 1
    using ONLY CTX_LO (ROUND_FLOOR) and CTX_HI (ROUND_CEILING) +, -, *, / and geometric tail remainder.
    """
    t2_lo = CTX_LO.multiply(t_lo, t_lo)
    t2_hi = CTX_HI.multiply(t_hi, t_hi)
    p_lo = t_lo
    p_hi = t_hi
    s_lo = t_lo
    s_hi = t_hi
    for k in range(1, n_terms):
        d = Decimal(2 * k + 1)
        p_lo = CTX_LO.multiply(p_lo, t2_lo)
        p_hi = CTX_HI.multiply(p_hi, t2_hi)
        s_lo = CTX_LO.add(s_lo, CTX_LO.divide(p_lo, d))
        s_hi = CTX_HI.add(s_hi, CTX_HI.divide(p_hi, d))
    p_hi = CTX_HI.multiply(p_hi, t2_hi)
    rem = CTX_HI.divide(p_hi, CTX_LO.multiply(Decimal(2 * n_terms + 1), CTX_LO.subtract(_D1, t2_hi)))
    s_hi = CTX_HI.add(s_hi, rem)
    return CTX_LO.multiply(_D2, s_lo), CTX_HI.multiply(_D2, s_hi)


# Precompute rational artanh anchor ladder from x_0 = 1 (ln(1) = 0) up to 2.5 * 10^{11} using ONLY +, -, *, /:
_ANCHOR_X = [1]
_ANCHOR_LN_LO = [_D0]
_ANCHOR_LN_HI = [_D0]
_cur_a = 1
while _cur_a < 250000000000:
    _nxt_a = max(_cur_a + 1, int(_cur_a * 1.015))
    _num_a = Decimal(_nxt_a - _cur_a)
    _den_a = Decimal(_nxt_a + _cur_a)
    _nt_a = 28 if _cur_a < 50 else 6
    _d_lo, _d_hi = _artanh_exact_dec(CTX_LO.divide(_num_a, _den_a), CTX_HI.divide(_num_a, _den_a), _nt_a)
    _ANCHOR_X.append(_nxt_a)
    _ANCHOR_LN_LO.append(CTX_LO.add(_ANCHOR_LN_LO[-1], _d_lo))
    _ANCHOR_LN_HI.append(CTX_HI.add(_ANCHOR_LN_HI[-1], _d_hi))
    _cur_a = _nxt_a
_ANCHOR_F_LO = [_NA(float(v), _NINF) if i > 0 else 0.0 for i, v in enumerate(_ANCHOR_LN_LO)]
_ANCHOR_F_HI = [_NA(float(v), _INF) if i > 0 else 0.0 for i, v in enumerate(_ANCHOR_LN_HI)]


def _ln_pure_dec(x_lo: Decimal, x_hi: Decimal):
    assert x_lo > _D0 and x_lo <= x_hi
    if x_lo < _D1:
        if x_hi <= _D1:
            inv_lo = max(_D1, CTX_LO.divide(_D1, x_hi))
            inv_hi = max(_D1, CTX_HI.divide(_D1, x_lo))
            l_lo, l_hi = _ln_pure_dec(inv_lo, inv_hi)
            return CTX_LO.minus(l_hi), (_D0 if x_hi == _D1 else CTX_HI.minus(l_lo))
        inv_hi = max(_D1, CTX_HI.divide(_D1, x_lo))
        _, l_hi_inv = _ln_pure_dec(_D1, inv_hi)
        _, l_hi = _ln_pure_dec(_D1, x_hi)
        return CTX_LO.minus(l_hi_inv), l_hi
    idx_lo = max(0, min(len(_ANCHOR_X) - 1, bisect.bisect_right(_ANCHOR_X, float(x_lo)) - 1))
    while idx_lo > 0 and Decimal(_ANCHOR_X[idx_lo]) > x_lo:
        idx_lo -= 1
    while idx_lo + 1 < len(_ANCHOR_X) and Decimal(_ANCHOR_X[idx_lo + 1]) <= x_lo:
        idx_lo += 1
    a_lo = Decimal(_ANCHOR_X[idx_lo])
    t_lo = CTX_LO.divide(CTX_LO.subtract(x_lo, a_lo), CTX_HI.add(x_lo, a_lo))
    if x_lo == x_hi:
        t_hi = CTX_HI.divide(CTX_HI.subtract(x_hi, a_lo), CTX_LO.add(x_hi, a_lo))
        d_lo, d_hi = _artanh_exact_dec(t_lo, t_hi, 6)
        res_lo = CTX_LO.add(_ANCHOR_LN_LO[idx_lo], d_lo)
        res_hi = CTX_HI.add(_ANCHOR_LN_HI[idx_lo], d_hi)
        assert res_lo <= res_hi
        return res_lo, res_hi
    d_lo, _ = _artanh_exact_dec(t_lo, t_lo, 6)
    res_lo = CTX_LO.add(_ANCHOR_LN_LO[idx_lo], d_lo)

    idx_hi = max(0, min(len(_ANCHOR_X) - 1, bisect.bisect_right(_ANCHOR_X, float(x_hi)) - 1))
    while idx_hi > 0 and Decimal(_ANCHOR_X[idx_hi]) > x_hi:
        idx_hi -= 1
    while idx_hi + 1 < len(_ANCHOR_X) and Decimal(_ANCHOR_X[idx_hi + 1]) <= x_hi:
        idx_hi += 1
    a_hi = Decimal(_ANCHOR_X[idx_hi])
    t_hi = CTX_HI.divide(CTX_HI.subtract(x_hi, a_hi), CTX_LO.add(x_hi, a_hi))
    _, d_hi = _artanh_exact_dec(t_hi, t_hi, 6)
    res_hi = CTX_HI.add(_ANCHOR_LN_HI[idx_hi], d_hi)
    assert res_lo <= res_hi
    return res_lo, res_hi


def _ln_lo_only(x_lo: float) -> float:
    idx_lo = bisect.bisect_right(_ANCHOR_X, x_lo) - 1
    a_lo = float(_ANCHOR_X[idx_lo])
    t_lo = _NA(_NA(x_lo - a_lo, _NINF) / _NA(x_lo + a_lo, _INF), _NINF)
    t2_lo = _NA(t_lo * t_lo, _NINF)
    t3_lo = _NA(t2_lo * t_lo, _NINF)
    t5_lo = _NA(t3_lo * t2_lo, _NINF)
    t7_lo = _NA(t5_lo * t2_lo, _NINF)
    d_lo = _NA(
        2.0 * _NA(t_lo + _NA(_NA(t3_lo / 3.0, _NINF) + _NA(_NA(t5_lo / 5.0, _NINF) + _NA(t7_lo / 7.0, _NINF), _NINF), _NINF), _NINF),
        _NINF,
    )
    return _NA(_ANCHOR_F_LO[idx_lo] + d_lo, _NINF)


def _ln_hi_only(x_hi: float) -> float:
    idx_hi = bisect.bisect_right(_ANCHOR_X, x_hi) - 1
    a_hi = float(_ANCHOR_X[idx_hi])
    t_hi = _NA(_NA(x_hi - a_hi, _INF) / _NA(x_hi + a_hi, _NINF), _INF)
    t2_hi = _NA(t_hi * t_hi, _INF)
    t3_hi = _NA(t2_hi * t_hi, _INF)
    t5_hi = _NA(t3_hi * t2_hi, _INF)
    t7_hi = _NA(t5_hi * t2_hi, _INF)
    t9_rem = _NA(_NA(t7_hi * t2_hi, _INF) / _NA(9.0 * _NA(1.0 - t2_hi, _NINF), _NINF), _INF)
    d_hi = _NA(
        2.0
        * _NA(
            t_hi
            + _NA(
                _NA(t3_hi / 3.0, _INF)
                + _NA(_NA(t5_hi / 5.0, _INF) + _NA(_NA(t7_hi / 7.0, _INF) + t9_rem, _INF), _INF),
                _INF,
            ),
            _INF,
        ),
        _INF,
    )
    return _NA(_ANCHOR_F_HI[idx_hi] + d_hi, _INF)


def _ln_pure_flt(x_lo: float, x_hi: float):
    assert x_lo > 0.0 and x_lo <= x_hi
    if x_lo < 1.0:
        if x_hi <= 1.0:
            inv_lo = max(1.0, _NA(1.0 / x_hi, _NINF))
            inv_hi = max(1.0, _NA(1.0 / x_lo, _INF))
            l_lo, l_hi = _ln_pure_flt(inv_lo, inv_hi)
            return -l_hi, (0.0 if x_hi == 1.0 else -l_lo)
        inv_hi = max(1.0, _NA(1.0 / x_lo, _INF))
        _, l_hi_inv = _ln_pure_flt(1.0, inv_hi)
        _, l_hi = _ln_pure_flt(1.0, x_hi)
        return -l_hi_inv, l_hi
    idx_lo = max(0, min(len(_ANCHOR_X) - 1, bisect.bisect_right(_ANCHOR_X, x_lo) - 1))
    a_lo = float(_ANCHOR_X[idx_lo])
    t_lo = _NA(_NA(x_lo - a_lo, _NINF) / _NA(x_lo + a_lo, _INF), _NINF)
    t2_lo = _NA(t_lo * t_lo, _NINF)
    t3_lo = _NA(t2_lo * t_lo, _NINF)
    t5_lo = _NA(t3_lo * t2_lo, _NINF)
    t7_lo = _NA(t5_lo * t2_lo, _NINF)
    d_lo = _NA(
        2.0 * _NA(t_lo + _NA(_NA(t3_lo / 3.0, _NINF) + _NA(_NA(t5_lo / 5.0, _NINF) + _NA(t7_lo / 7.0, _NINF), _NINF), _NINF), _NINF),
        _NINF,
    )
    res_lo = _NA(_ANCHOR_F_LO[idx_lo] + d_lo, _NINF)

    idx_hi = idx_lo if x_lo == x_hi else max(0, min(len(_ANCHOR_X) - 1, bisect.bisect_right(_ANCHOR_X, x_hi) - 1))
    a_hi = float(_ANCHOR_X[idx_hi])
    t_hi = _NA(_NA(x_hi - a_hi, _INF) / _NA(x_hi + a_hi, _NINF), _INF)
    t2_hi = _NA(t_hi * t_hi, _INF)
    t3_hi = _NA(t2_hi * t_hi, _INF)
    t5_hi = _NA(t3_hi * t2_hi, _INF)
    t7_hi = _NA(t5_hi * t2_hi, _INF)
    t9_rem = _NA(_NA(t7_hi * t2_hi, _INF) / _NA(9.0 * _NA(1.0 - t2_hi, _NINF), _NINF), _INF)
    d_hi = _NA(
        2.0
        * _NA(
            t_hi
            + _NA(
                _NA(t3_hi / 3.0, _INF)
                + _NA(_NA(t5_hi / 5.0, _INF) + _NA(_NA(t7_hi / 7.0, _INF) + t9_rem, _INF), _INF),
                _INF,
            ),
            _INF,
        ),
        _INF,
    )
    res_hi = _NA(_ANCHOR_F_HI[idx_hi] + d_hi, _INF)
    assert res_lo <= res_hi
    return res_lo, res_hi


def _exp_pure_dec(x_lo: Decimal, x_hi: Decimal):
    """
    Rigorous enclosure of exp([x_lo, x_hi]) using ONLY 16-term Taylor series + Lagrange remainder
    in CTX_LO / CTX_HI (+, -, *, /).
    """
    res = []
    for x, is_hi in ((x_lo, False), (x_hi, True)):
        if x == _D0:
            res.append(_D1)
            continue
        k_sc = 0
        u_lo = u_hi = x
        while abs(u_hi) > Decimal("0.0625"):
            u_lo = CTX_LO.divide(u_lo, _D2)
            u_hi = CTX_HI.divide(u_hi, _D2)
            k_sc += 1
        sum_lo = sum_hi = _D1
        p_lo = p_hi = _D1
        for m in range(1, 17):
            dm = Decimal(m)
            p1 = CTX_LO.multiply(p_lo, u_lo); p2 = CTX_LO.multiply(p_lo, u_hi)
            p3 = CTX_LO.multiply(p_hi, u_lo); p4 = CTX_LO.multiply(p_hi, u_hi)
            q1 = CTX_HI.multiply(p_lo, u_lo); q2 = CTX_HI.multiply(p_lo, u_hi)
            q3 = CTX_HI.multiply(p_hi, u_lo); q4 = CTX_HI.multiply(p_hi, u_hi)
            p_lo = CTX_LO.divide(min(p1, p2, p3, p4), dm)
            p_hi = CTX_HI.divide(max(q1, q2, q3, q4), dm)
            sum_lo = CTX_LO.add(sum_lo, p_lo)
            sum_hi = CTX_HI.add(sum_hi, p_hi)
        u_abs = max(abs(u_lo), abs(u_hi))
        rem = CTX_HI.divide(CTX_HI.multiply(_D2, CTX_HI.power(u_abs, Decimal(17))), _FACT17)
        v = CTX_HI.add(sum_hi, rem) if is_hi else CTX_LO.subtract(sum_lo, rem)
        ctx = CTX_HI if is_hi else CTX_LO
        for _ in range(k_sc):
            v = ctx.multiply(v, v)
        res.append(v)
    assert res[0] <= res[1]
    return res[0], res[1]


class FInterval:
    """
    Self-certifying IEEE-754 interval [lo, hi] using math.nextafter:
    - Integer inputs of arbitrary size are verified by exact integer comparison int(lo) <= n <= int(hi).
    - Square roots are verified by directed-rounded multiplication lo*lo <= self.lo and hi*hi >= self.hi.
    - Logarithms and exponentials are evaluated from rational artanh and Taylor series using only +, -, *, /.
    """

    __slots__ = ("lo", "hi")

    def __init__(self, lo: float, hi: float = None):
        if isinstance(lo, FInterval):
            self.lo, self.hi = lo.lo, lo.hi
        elif hi is None:
            if isinstance(lo, int):
                f = float(lo)
                if int(f) == lo:
                    self.lo = self.hi = f
                elif int(f) < lo:
                    self.lo = f
                    self.hi = _NA(f, _INF)
                else:
                    self.lo = _NA(f, _NINF)
                    self.hi = f
                assert int(self.lo) <= lo <= int(self.hi)
            else:
                f = float(lo)
                self.lo = _NA(f, _NINF)
                self.hi = _NA(f, _INF)
        else:
            self.lo = float(lo)
            self.hi = float(hi)
            assert self.lo <= self.hi, f"Invalid FInterval [{self.lo}, {self.hi}]"

    def __add__(self, o):
        if not isinstance(o, FInterval):
            o = FInterval(o)
        return FInterval(_NA(self.lo + o.lo, _NINF), _NA(self.hi + o.hi, _INF))

    __radd__ = __add__

    def __sub__(self, o):
        if not isinstance(o, FInterval):
            o = FInterval(o)
        return FInterval(_NA(self.lo - o.hi, _NINF), _NA(self.hi - o.lo, _INF))

    def __rsub__(self, o):
        if not isinstance(o, FInterval):
            o = FInterval(o)
        return o.__sub__(self)

    def __mul__(self, o):
        if not isinstance(o, FInterval):
            o = FInterval(o)
        if self.lo >= 0.0 and o.lo >= 0.0:
            return FInterval(_NA(self.lo * o.lo, _NINF), _NA(self.hi * o.hi, _INF))
        p1, p2, p3, p4 = self.lo * o.lo, self.lo * o.hi, self.hi * o.lo, self.hi * o.hi
        return FInterval(_NA(min(p1, p2, p3, p4), _NINF), _NA(max(p1, p2, p3, p4), _INF))

    __rmul__ = __mul__

    def __truediv__(self, o):
        if not isinstance(o, FInterval):
            o = FInterval(o)
        assert o.lo > 0.0, f"Division by FInterval containing <= 0: [{o.lo}, {o.hi}]"
        if self.lo >= 0.0:
            return FInterval(_NA(self.lo / o.hi, _NINF), _NA(self.hi / o.lo, _INF))
        q1, q2, q3, q4 = self.lo / o.lo, self.lo / o.hi, self.hi / o.lo, self.hi / o.hi
        return FInterval(_NA(min(q1, q2, q3, q4), _NINF), _NA(max(q1, q2, q3, q4), _INF))

    def __rtruediv__(self, o):
        if not isinstance(o, FInterval):
            o = FInterval(o)
        return o.__truediv__(self)

    def sqrt(self):
        x_lo = max(0.0, self.lo)
        x_hi = max(0.0, self.hi)
        if x_lo == 0.0:
            s = 0.0
        else:
            s = math.sqrt(x_lo)
            while s > 0.0 and _NA(s * s, _INF) > x_lo:
                s = _NA(s, _NINF)
            assert s == 0.0 or _NA(s * s, _INF) <= x_lo
        if x_hi == 0.0:
            t = 0.0
        else:
            t = math.sqrt(x_hi)
            while _NA(t * t, _NINF) < x_hi:
                t = _NA(t, _INF)
            assert _NA(t * t, _NINF) >= x_hi
        return FInterval(s, t)

    def ln(self):
        l_lo, l_hi = _ln_pure_flt(self.lo, self.hi)
        return FInterval(l_lo, l_hi)

    def exp(self):
        e_lo, e_hi = _exp_pure_dec(Decimal.from_float(self.lo), Decimal.from_float(self.hi))
        return FInterval(_NA(float(e_lo), _NINF), _NA(float(e_hi), _INF))


class DInterval:
    """
    Self-certifying 26-digit decimal.Decimal interval [lo, hi] using ROUND_FLOOR and ROUND_CEILING contexts:
    - Square roots are verified by CTX_HI.multiply(s, s) <= self.lo and CTX_LO.multiply(t, t) >= self.hi.
    - Logarithms and exponentials are evaluated purely from rational artanh and Taylor series using only +, -, *, /.
    """

    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi=None):
        if isinstance(lo, DInterval):
            self.lo, self.hi = lo.lo, lo.hi
        elif isinstance(lo, FInterval):
            self.lo = CTX_LO.plus(Decimal.from_float(lo.lo))
            self.hi = CTX_HI.plus(Decimal.from_float(lo.hi))
        elif hi is None:
            if isinstance(lo, (int, Decimal, str)):
                d = Decimal(lo)
                self.lo = CTX_LO.plus(d)
                self.hi = CTX_HI.plus(d)
            else:
                self.lo = CTX_LO.plus(Decimal.from_float(_NA(float(lo), _NINF)))
                self.hi = CTX_HI.plus(Decimal.from_float(_NA(float(lo), _INF)))
        else:
            self.lo = lo if isinstance(lo, Decimal) else (
                CTX_LO.plus(Decimal(lo)) if isinstance(lo, (int, str)) else CTX_LO.plus(Decimal.from_float(_NA(float(lo), _NINF)))
            )
            self.hi = hi if isinstance(hi, Decimal) else (
                CTX_HI.plus(Decimal(hi)) if isinstance(hi, (int, str)) else CTX_HI.plus(Decimal.from_float(_NA(float(hi), _INF)))
            )
            assert self.lo <= self.hi, f"Invalid DInterval [{self.lo}, {self.hi}]"

    def __add__(self, o):
        if not isinstance(o, DInterval):
            o = DInterval(o)
        return DInterval(CTX_LO.add(self.lo, o.lo), CTX_HI.add(self.hi, o.hi))

    __radd__ = __add__

    def __sub__(self, o):
        if not isinstance(o, DInterval):
            o = DInterval(o)
        return DInterval(CTX_LO.subtract(self.lo, o.hi), CTX_HI.subtract(self.hi, o.lo))

    def __rsub__(self, o):
        if not isinstance(o, DInterval):
            o = DInterval(o)
        return o.__sub__(self)

    def __mul__(self, o):
        if not isinstance(o, DInterval):
            o = DInterval(o)
        if self.lo >= _D0 and o.lo >= _D0:
            return DInterval(CTX_LO.multiply(self.lo, o.lo), CTX_HI.multiply(self.hi, o.hi))
        p_lo = (
            CTX_LO.multiply(self.lo, o.lo), CTX_LO.multiply(self.lo, o.hi),
            CTX_LO.multiply(self.hi, o.lo), CTX_LO.multiply(self.hi, o.hi),
        )
        p_hi = (
            CTX_HI.multiply(self.lo, o.lo), CTX_HI.multiply(self.lo, o.hi),
            CTX_HI.multiply(self.hi, o.lo), CTX_HI.multiply(self.hi, o.hi),
        )
        return DInterval(min(p_lo), max(p_hi))

    __rmul__ = __mul__

    def __truediv__(self, o):
        if not isinstance(o, DInterval):
            o = DInterval(o)
        assert o.lo > _D0
        if self.lo >= _D0:
            return DInterval(CTX_LO.divide(self.lo, o.hi), CTX_HI.divide(self.hi, o.lo))
        q_lo = (
            CTX_LO.divide(self.lo, o.lo), CTX_LO.divide(self.lo, o.hi),
            CTX_LO.divide(self.hi, o.lo), CTX_LO.divide(self.hi, o.hi),
        )
        q_hi = (
            CTX_HI.divide(self.lo, o.lo), CTX_HI.divide(self.lo, o.hi),
            CTX_HI.divide(self.hi, o.lo), CTX_HI.divide(self.hi, o.hi),
        )
        return DInterval(min(q_lo), max(q_hi))

    def __rtruediv__(self, o):
        if not isinstance(o, DInterval):
            o = DInterval(o)
        return o.__truediv__(self)

    def sqrt(self):
        x_lo = max(_D0, self.lo)
        x_hi = max(_D0, self.hi)
        s = _D0 if x_lo == _D0 else CTX_LO.sqrt(x_lo)
        while s > _D0 and CTX_HI.multiply(s, s) > x_lo:
            s = CTX_LO.next_minus(s)
        t = _D0 if x_hi == _D0 else CTX_HI.sqrt(x_hi)
        while CTX_LO.multiply(t, t) < x_hi:
            t = CTX_HI.next_plus(t)
        assert CTX_HI.multiply(s, s) <= x_lo and CTX_LO.multiply(t, t) >= x_hi
        return DInterval(s, t)

    def ln(self):
        l_lo, l_hi = _ln_pure_dec(self.lo, self.hi)
        return DInterval(l_lo, l_hi)

    def exp(self):
        e_lo, e_hi = _exp_pure_dec(self.lo, self.hi)
        return DInterval(e_lo, e_hi)


def ival_max(a, b, cls=FInterval):
    ia = a if isinstance(a, cls) else cls(a)
    ib = b if isinstance(b, cls) else cls(b)
    return cls(max(ia.lo, ib.lo), max(ia.hi, ib.hi))


def ival_min(a, b, cls=FInterval):
    ia = a if isinstance(a, cls) else cls(a)
    ib = b if isinstance(b, cls) else cls(b)
    return cls(min(ia.lo, ib.lo), min(ia.hi, ib.hi))


def sieve_primes(limit: int):
    is_p = bytearray([1]) * (limit + 1)
    is_p[0] = is_p[1] = 0
    for i in range(2, int(limit ** 0.5) + 1):
        if is_p[i]:
            is_p[i * i : limit + 1 : i] = bytearray(len(is_p[i * i : limit + 1 : i]))
    return [i for i, v in enumerate(is_p) if v]


PRIMES = sieve_primes(5000)
EPS_ROUND = 1e-11
SIGMA2_INF = 0.7553666109  # strict upper bound on sum_{p>=2, k>=2} log(p)/p^k = 0.75536661083...


def exact_rigorous_W_biconj_iv(
    p: int, K: int, S: int, R: int, W_main_iv, eps_J_iv, theta_iv, W2_norm_iv, cls=FInterval
):
    """
    Directed-rounding interval enclosure of w_keep(p) from Section 4.3 over integer subtriangle cuts L0 in {0, ..., S},
    including all even prime powers p^{2*ell} <= S (ell >= 1) via the pure-z' ASW tower B_s^{(p)}(z'),
    the exact finite row-count normalization 2*M_tri/W_main = (3/R)*(1 + 1/S), and the periodic mod-p
    remainder bound n*floor(p^2/4)/(p*W_main) from sum_{j=0}^{B-1}(j - floor(j/p)) = ((p-1)/(2p))*B^2 - r_B*(p-r_B)/(2p).
    """
    M_tri = R * (S + 1) // 2
    iv_M_tri = cls(M_tri)
    sum_s_all = 0
    p_pow = p * p
    while p_pow <= S:
        sum_s_all += sum_floor_s_tri(S, p_pow)
        p_pow *= (p * p)
    s_even_norm = cls(2 * K * sum_s_all) / W_main_iv
    c_shift2 = K + p - 1 - 2 * (p * p - 1)  # exact integer 2 * c_{K,p}
    iv_p = cls(p)
    iv_p2 = cls(p * p)
    iv_p3 = cls(p * p * p)
    iv_Kp = cls(K - p)
    iv_zero = cls(0)
    iv_1p1S = cls(S + 1) / cls(S)
    sum_L_all = S * (S + 1) // 2
    sum_LSL_all = (S * (S * S - 1)) // 6

    best_lo = None
    best_iv = None
    for idx in range(201):
        L0 = int(round((idx / 200.0) * S))
        sum_L_top = L0 * (L0 + 1) // 2
        sum_L_bot = sum_L_all - sum_L_top
        sum_LSL_top = S * sum_L_top - (L0 * (L0 + 1) * (2 * L0 + 1)) // 6
        sum_LSL_bot = sum_LSL_all - sum_LSL_top
        # 2*K*sum_LSL + 2*c_shift*sum_L is an exact integer
        num_top = 2 * K * sum_LSL_top + c_shift2 * sum_L_top
        num_bot = 2 * K * sum_LSL_bot + c_shift2 * sum_L_bot
        m_top = (iv_Kp * cls(num_top)) / iv_p2
        m_bot = (iv_Kp * cls(num_bot)) / iv_p3
        hermite_rem = cls((S - L0) * (K - p) * (p * p)) / cls(2)
        sum_s_L0 = 0
        p_pow = p * p
        while p_pow <= L0:
            sum_s_L0 += sum_floor_s_tri(L0, p_pow)
            p_pow *= (p * p)
        extra_s_top = cls(2 * (K - p) * max(0, sum_floor_s_tri(L0, p) - sum_s_L0))
        raw_gain = m_top + m_bot - hermite_rem + extra_s_top
        gain_norm = s_even_norm + ival_max(iv_zero, raw_gain, cls) / W_main_iv
        q0 = cls((K - p) * sum_L_top) / iv_M_tri
        rem_col = (iv_M_tri * cls(p * p // 4)) / (iv_p * theta_iv * eps_J_iv * cls(R) * W_main_iv) if L0 > 0 else iv_zero
        cost_col = cls(3) * iv_1p1S * q0 * (cls(1) - (q0 * theta_iv) / cls(2)) * (cls(p - 1) / iv_p) * eps_J_iv + rem_col
        val_iv = W2_norm_iv + gain_norm - cost_col
        if best_lo is None or val_iv.lo > best_lo:
            best_lo = val_iv.lo
            best_iv = val_iv
    return best_iv


def exact_rigorous_W_biconj(
    p: int, K: int, S: int, R: int, W_main: float, eps_J: float, theta: float, W2_norm: float
) -> float:
    return exact_rigorous_W_biconj_iv(
        p, K, S, R, FInterval(W_main), FInterval(eps_J), FInterval(theta), FInterval(W2_norm), FInterval
    ).lo


best_W_hermite_asw = exact_rigorous_W_biconj


def compute_save_deriv_exact_bins_iv(
    M_tri: int, R: int, S: int, J: int, theta_iv, slope_j_lo_iv, cls=FInterval, N_deriv: int = 3200
):
    """
    Certifies the uniform falling-factorial saving save_deriv by partitioning {1, ..., M_tri}
    into N_deriv = 3,200 exact integer index intervals (K_m, K_{m+1}] of exact cardinality
    cnt_m = K_{m+1} - K_m (zero discretization loss).
    """
    iv_0, iv_1, iv_3 = cls(0), cls(1), cls(3)
    iv_R, iv_S, iv_J, iv_M_tri = cls(R), cls(S), cls(J), cls(M_tri)
    exp_neg_slope = (iv_0 - slope_j_lo_iv).exp()
    K_pts = [int(M_tri * (1.0 - (1.0 - m / float(N_deriv)) ** 2)) for m in range(N_deriv + 1)]
    K_pts[0] = 0
    K_pts[N_deriv] = M_tri
    deriv_r_saving_lb = iv_0
    for m in range(N_deriv):
        cnt = K_pts[m + 1] - K_pts[m]
        if cnt <= 0:
            continue
        G_lo_iv = cls(K_pts[m] + 1) / iv_M_tri
        G_hi_iv = cls(K_pts[m + 1]) / iv_M_tri
        u_hi_iv = iv_1 - ival_max(iv_0, iv_1 - G_hi_iv, cls).sqrt()
        j_low_u = ival_max(iv_0, (iv_1 - theta_iv * (iv_1 - G_lo_iv)) * iv_J, cls) / iv_R
        r_u = ival_min(iv_1, (iv_1 + iv_1 / iv_S) * u_hi_iv + iv_1 / iv_R, cls)
        j_star = ival_max(iv_0, ival_min(j_low_u, r_u - exp_neg_slope, cls), cls)
        if j_star.hi <= 0:
            g_max = iv_0
        else:
            rem = r_u - j_star
            psi_int = r_u * r_u.ln() - rem * rem.ln() - j_star
            g_max = ival_max(iv_0, j_star * slope_j_lo_iv + psi_int, cls)
        save_u = ival_max(iv_0, j_low_u * slope_j_lo_iv - g_max, cls)
        weight_step = cls(cnt) / iv_M_tri
        deriv_r_saving_lb = deriv_r_saving_lb + weight_step * iv_3 * save_u
    return deriv_r_saving_lb


# Sieve primes up to 9,000,000 and precompute exact dyadic integer prefix sums L_p = 2^53 * lp_lo(p) in Z:
P_ALL = sieve_primes(9000000)
PREF_L0 = [0] * (len(P_ALL) + 1)
PREF_L1 = [0] * (len(P_ALL) + 1)
PREF_L2 = [0] * (len(P_ALL) + 1)
_n_anch = len(_ANCHOR_X)
_idx_a = 0
_a_lo = float(_ANCHOR_X[0])
_f_lo = _ANCHOR_F_LO[0]
_next_a = _ANCHOR_X[1]
_acc0 = _acc1 = _acc2 = 0
for _i_p, _p in enumerate(P_ALL):
    while _idx_a + 1 < _n_anch and _p >= _next_a:
        _idx_a += 1
        _a_lo = float(_ANCHOR_X[_idx_a])
        _f_lo = _ANCHOR_F_LO[_idx_a]
        _next_a = _ANCHOR_X[_idx_a + 1] if _idx_a + 1 < _n_anch else 10 ** 18
    _fp = float(_p)
    _t_lo = _NA(_NA(_fp - _a_lo, _NINF) / _NA(_fp + _a_lo, _INF), _NINF)
    _t2_lo = _NA(_t_lo * _t_lo, _NINF)
    _t3_lo = _NA(_t2_lo * _t_lo, _NINF)
    _t5_lo = _NA(_t3_lo * _t2_lo, _NINF)
    _t7_lo = _NA(_t5_lo * _t2_lo, _NINF)
    _d_lo = _NA(2.0 * _NA(_t_lo + _NA(_NA(_t3_lo / 3.0, _NINF) + _NA(_NA(_t5_lo / 5.0, _NINF) + _NA(_t7_lo / 7.0, _NINF), _NINF), _NINF), _NINF), _NINF)
    _lp_lo = _NA(_f_lo + _d_lo, _NINF)
    _Lp = int(math.ldexp(_lp_lo, 53))
    _pL = _p * _Lp
    _acc0 += _Lp
    _acc1 += _pL
    _acc2 += _p * _pL
    PREF_L0[_i_p + 1] = _acc0
    PREF_L1[_i_p + 1] = _acc1
    PREF_L2[_i_p + 1] = _acc2
E_MERTENS = -1.3325822757332209

# Precompute universal prime-power floor array PP_FL[j] = sum_{p>=2, ell>=2} floor(j/p^ell)*lp_lo(p) up to Q0_MAX = 710,000:
Q0_MAX = 710000
_pp_diff = [0.0] * (Q0_MAX + 1)
for _p in PRIMES:
    _pk = _p * _p
    if _pk > Q0_MAX:
        break
    _lp_lo = FInterval(_p).ln().lo
    while _pk <= Q0_MAX:
        for _m in range(_pk, Q0_MAX + 1, _pk):
            _pp_diff[_m] = _NA(_pp_diff[_m] + _lp_lo, _NINF)
        _pk *= _p
PP_FL = [0.0] * (Q0_MAX + 1)
_cur_pp = 0.0
for _j in range(Q0_MAX + 1):
    _cur_pp = _NA(_cur_pp + _pp_diff[_j], _NINF)
    PP_FL[_j] = _cur_pp
del _pp_diff


def S_r_exact(R: int, K: int, p: int) -> int:
    """
    Exact integer evaluation of S_r(R, K, p) = 2 * Sigma_tri(R, p) + (K - 1) * sum_{r=0}^{R-1} floor(r / p)
    = sum_{m=1}^{floor(R/p)} (R - m*p)*(R + K - m*p) = A_q - B_q*p + C_q*p^2 (Lemma 4.2).
    """
    q = R // p
    if q <= 0:
        return 0
    return q * R * (R + K) - ((q * (q + 1)) >> 1) * (2 * R + K) * p + ((q * (q + 1) * (2 * q + 1)) // 6) * p * p


def fast_sum_Sr_Lp(R: int, K: int, P_max: int) -> int:
    """
    Exact integer evaluation of sum_{K <= p <= P_max} S_r(R, K, p) * L_p (where L_p = 2^53 * lp_lo(p) in Z)
    in O(sqrt(R)) time by grouping primes p with identical quotient q = floor(R / p).
    """
    idx_lo = bisect.bisect_left(P_ALL, K)
    idx_hi = bisect.bisect_right(P_ALL, min(P_max, R))
    if idx_lo >= idx_hi:
        return 0
    RRK = R * (R + K)
    RK2 = 2 * R + K
    split_idx = min(idx_hi, 300)
    tot = 0
    for i in range(idx_lo, split_idx):
        p = P_ALL[i]
        q = R // p
        sr = q * RRK - ((q * (q + 1)) >> 1) * RK2 * p + ((q * (q + 1) * (2 * q + 1)) // 6) * p * p
        tot += sr * (PREF_L0[i + 1] - PREF_L0[i])
    if split_idx < idx_hi:
        q_max = R // P_ALL[split_idx]
        q_min = max(1, R // P_ALL[idx_hi - 1])
        cur_hi = idx_hi
        for q in range(q_min, q_max + 1):
            p_left = R // (q + 1)
            nxt_lo = max(split_idx, bisect.bisect_right(P_ALL, p_left, split_idx, cur_hi))
            if nxt_lo < cur_hi:
                A_q = q * RRK
                B_q = ((q * (q + 1)) >> 1) * RK2
                C_q = (q * (q + 1) * (2 * q + 1)) // 6
                s0 = PREF_L0[cur_hi] - PREF_L0[nxt_lo]
                s1 = PREF_L1[cur_hi] - PREF_L1[nxt_lo]
                s2 = PREF_L2[cur_hi] - PREF_L2[nxt_lo]
                tot += A_q * s0 - B_q * s1 + C_q * s2
                cur_hi = nxt_lo
            if cur_hi <= split_idx:
                break
    return tot


_HYBRID_PADIC_CACHE = {}


def sum_floor_range(N: int, m: int) -> int:
    if N <= 0:
        return 0
    q = N // m
    r = N % m
    return m * q * (q - 1) // 2 + r * q


def col_split_floor_total(p: int, n: int, M_tri: int) -> int:
    q_cols = M_tri // n
    r_cols = M_tri % n
    if p > q_cols:
        return 0
    s_low = sum_floor_range(q_cols, p)
    return n * s_low + r_cols * (q_cols // p)


