"""Numerical support for the determinant comparison. Source history is in the paper.

Retained function bodies are unchanged. Unused top-level functions and the
standalone historical demonstration are omitted. See ../README.md for scope.
"""
import array, bisect, gc, math, os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import verify_jet_disk as vjd
import verify_fubini_jensen_c1 as vfjc


def _consts(cls):
    i0, i1, i2, i3, i4 = cls(0), cls(1), cls(2), cls(3), cls(4)
    pi = (cls(vjd.Decimal("3.14159265358979323846264338"), vjd.Decimal("3.14159265358979323846264339"))
          if cls is vjd.DInterval else vjd.FInterval(math.pi))
    em = (cls(vjd.Decimal("-1.33258227573322089"), vjd.Decimal("-1.33258227573322087"))
          if cls is vjd.DInterval else vjd.FInterval(vjd.E_MERTENS))
    return i0, i1, i2, i3, i4, pi, i3.sqrt(), em


_NA, _INF, _NINF = vjd._NA, vjd._INF, vjd._NINF
_RAW_CAND_CACHE = {}
_P_HIGH_BLKS = []
_P_HIGH_MAX = 9000000
_SMALL_ODD_PRIMES = []


def _sieve_small_interval_odd(pa: int, pb: int, small_odd_primes) -> list[int]:
    if pa > pb:
        return []
    low_val = pa | 1
    high_val = pb if (pb & 1) else (pb - 1)
    if low_val > high_val:
        return []
    seg_len = ((high_val - low_val) >> 1) + 1
    seg = bytearray([1]) * seg_len
    max_p = int(high_val ** 0.5)
    for p in small_odd_primes:
        if p > max_p:
            break
        start_val = p * p
        if start_val < low_val:
            rem = low_val % p
            start_val = low_val if rem == 0 else (low_val + (p - rem))
            if (start_val & 1) == 0:
                start_val += p
        start_idx = (start_val - low_val) >> 1
        if start_idx < seg_len:
            seg[start_idx:seg_len:p] = bytearray((seg_len - 1 - start_idx) // p + 1)
    return [low_val + (i << 1) for i, v in enumerate(seg) if v]


def ensure_tables_up_to(P_max_target: int, Q0_target: int):
    global _P_HIGH_BLKS, _P_HIGH_MAX, _SMALL_ODD_PRIMES
    if P_max_target > _P_HIGH_MAX:
        _RAW_CAND_CACHE.clear()
        _P_HIGH_BLKS = []
        gc.collect()
        limit = max(P_max_target + 200, 312000200)
        sqrt_lim = int(limit ** 0.5) + 1
        half_sq = sqrt_lim >> 1
        sieve_small = bytearray([1]) * (half_sq + 1)
        sieve_small[0] = 0
        for i in range(1, (int(sqrt_lim ** 0.5) >> 1) + 1):
            if sieve_small[i]:
                p = (i << 1) | 1
                start = (p * p) >> 1
                sieve_small[start : half_sq + 1 : p] = bytearray(len(range(start, half_sq + 1, p)))
        _SMALL_ODD_PRIMES = [(i << 1) | 1 for i in range(1, half_sq + 1) if sieve_small[i]]

        _P_HIGH_BLKS = []
        seg_half_len = 16000000
        half_total = limit >> 1
        cur_low_idx = (9000001) >> 1
        buf_pa = buf_cnt = buf_s1 = buf_s2 = buf_s3 = last_p = 0

        while cur_low_idx <= half_total:
            cur_high_idx = min(half_total, cur_low_idx + seg_half_len - 1)
            seg_len = cur_high_idx - cur_low_idx + 1
            seg = bytearray([1]) * seg_len
            low_val = (cur_low_idx << 1) | 1
            high_val = (cur_high_idx << 1) | 1
            max_p = int(high_val ** 0.5)
            for p in _SMALL_ODD_PRIMES:
                if p > max_p:
                    break
                start_val = p * p
                if start_val < low_val:
                    rem = low_val % p
                    start_val = low_val if rem == 0 else (low_val + (p - rem))
                    if (start_val & 1) == 0:
                        start_val += p
                start_idx = (start_val >> 1) - cur_low_idx
                if start_idx < seg_len:
                    seg[start_idx:seg_len:p] = bytearray((seg_len - 1 - start_idx) // p + 1)

            for i, v in enumerate(seg):
                if v:
                    p = ((cur_low_idx + i) << 1) | 1
                    if buf_cnt == 0:
                        buf_pa = p
                    buf_cnt += 1
                    buf_s1 += p
                    p2 = p * p
                    buf_s2 += p2
                    buf_s3 += p2 * p
                    last_p = p
                    if buf_cnt == 256:
                        _P_HIGH_BLKS.append((buf_pa, last_p, 256, buf_s1, buf_s2, buf_s3))
                        buf_cnt = buf_s1 = buf_s2 = buf_s3 = 0
            cur_low_idx = cur_high_idx + 1

        if buf_cnt > 0:
            _P_HIGH_BLKS.append((buf_pa, last_p, buf_cnt, buf_s1, buf_s2, buf_s3))
        _P_HIGH_MAX = limit
        gc.collect()

    n_blk = (max(Q0_target, 24000000) >> 5) + 2
    if not hasattr(vjd, "PP_FL_STEP32") or vjd.PP_FL_STEP32 is None or len(vjd.PP_FL_STEP32) < n_blk:
        _RAW_CAND_CACHE.clear()
        vjd.PP_FL_STEP32 = None
        gc.collect()
        q_max = n_blk << 5
        pp_blk = array.array("d", [0.0]) * (n_blk + 1)
        for p in vjd.PRIMES:
            pk = p * p
            if pk > q_max:
                break
            lp_lo = vjd.FInterval(p).ln().lo
            while pk <= q_max:
                for m in range(pk, q_max + 1, pk):
                    idx_b = (m + 31) >> 5
                    if idx_b <= n_blk:
                        pp_blk[idx_b] = _NA(pp_blk[idx_b] + lp_lo, _NINF)
                pk *= p
        cur_pp = 0.0
        for b_i in range(n_blk):
            cur_pp = _NA(cur_pp + pp_blk[b_i], _NINF)
            pp_blk[b_i] = cur_pp
        vjd.PP_FL_STEP32 = pp_blk


def fast_sum_Sr_Lp_ext(R: int, K: int, P_max: int) -> int:
    sr_key = ("sr_ext", R, K, P_max)
    if sr_key in vjd._HYBRID_PADIC_CACHE:
        return vjd._HYBRID_PADIC_CACHE[sr_key]
    if P_max <= 9000000:
        res = vjd.fast_sum_Sr_Lp(R, K, P_max)
        vjd._HYBRID_PADIC_CACHE[sr_key] = res
        return res
    tot = vjd.fast_sum_Sr_Lp(R, K, 9000000)
    limit_p = min(P_max, R)
    RRK = R * (R + K)
    RK2 = 2 * R + K
    ONE53 = 1 << 53
    for pa, pb, s0, s1, s2, s3 in _P_HIGH_BLKS:
        if pa > limit_p:
            break
        q = R // pa
        if q <= 0:
            break
        max_p_q = min(limit_p, R // q)
        if pb <= max_p_q:
            Aq = q * RRK
            Bq = ((q * (q + 1)) >> 1) * RK2
            Cq = (q * (q + 1) * (2 * q + 1)) // 6
            sum_sr = Aq * s0 - Bq * s1 + Cq * s2
            sum_sr_dp = Aq * (s1 - pa * s0) - Bq * (s2 - pa * s1) + Cq * (s3 - pa * s2)
            base_L = int(math.ldexp(vjd._ln_lo_only(float(pa)), 53))
            slope_L = ONE53 // pb
            tot += sum_sr * base_L + sum_sr_dp * slope_L
        else:
            sub_ps = _sieve_small_interval_odd(pa, min(pb, limit_p), _SMALL_ODD_PRIMES)
            n_sub = len(sub_ps)
            i0 = 0
            while i0 < n_sub:
                pa_sub = sub_ps[i0]
                q_sub = R // pa_sub
                if q_sub <= 0:
                    break
                max_pq_sub = min(limit_p, R // q_sub)
                i1 = bisect.bisect_right(sub_ps, max_pq_sub, i0, n_sub)
                pb_sub = sub_ps[i1 - 1]
                s0_sub = i1 - i0
                s1_sub = s2_sub = s3_sub = 0
                for idx in range(i0, i1):
                    p = sub_ps[idx]
                    s1_sub += p
                    p2 = p * p
                    s2_sub += p2
                    s3_sub += p2 * p
                Aq = q_sub * RRK
                Bq = ((q_sub * (q_sub + 1)) >> 1) * RK2
                Cq = (q_sub * (q_sub + 1) * (2 * q_sub + 1)) // 6
                sum_sr = Aq * s0_sub - Bq * s1_sub + Cq * s2_sub
                sum_sr_dp = Aq * (s1_sub - pa_sub * s0_sub) - Bq * (s2_sub - pa_sub * s1_sub) + Cq * (s3_sub - pa_sub * s2_sub)
                base_L = int(math.ldexp(vjd._ln_lo_only(float(pa_sub)), 53))
                slope_L = ONE53 // pb_sub
                tot += sum_sr * base_L + sum_sr_dp * slope_L
                i0 = i1
    vjd._HYBRID_PADIC_CACHE[sr_key] = tot
    return tot


def get_raw_cands_cached(M_min: int, P_max: int, low_cut: int):
    key = (M_min, P_max, low_cut)
    if key in _RAW_CAND_CACHE:
        return _RAW_CAND_CACHE[key]
    _RAW_CAND_CACHE.clear()
    vjd._HYBRID_PADIC_CACHE.clear()
    gc.collect()
    low_x = array.array("i")
    low_y_spans = []
    high_by_y2 = []
    y = 1
    while (4 * M_min - 1) * y * y <= 4 * P_max:
        row_start = len(low_x)
        x0 = -1 if y == 2 else -((y - 1) // 2)
        y2 = y * y
        max_x2_xy = P_max - M_min * y2
        low_x2_xy_lim = low_cut - M_min * y2
        offsets = [d for d in range(y) if math.gcd(x0 + d, y) == 1]
        n_off = len(offsets)
        steps = [offsets[m + 1] - offsets[m] for m in range(n_off - 1)] + [offsets[0] + y - offsets[-1]]
        x = x0 + offsets[0]
        s_idx = 0
        blks = []
        b_x0 = b_xf = b_xl = b_cnt = b_d1 = b_d2 = b_d3 = 0
        while True:
            x2_xy = x * x + x * y
            if x2_xy > max_x2_xy:
                break
            if x2_xy <= low_x2_xy_lim:
                low_x.append(x)
            else:
                if b_cnt == 0:
                    b_x0 = x
                    b_xf = x2_xy
                b_xl = x2_xy
                b_cnt += 1
                b_d1 += x2_xy
                xv2 = x2_xy * x2_xy
                b_d2 += xv2
                b_d3 += xv2 * x2_xy
                if b_cnt == 256:
                    blks.append((b_x0, b_xf, b_xl, 256, b_d1, b_d2, b_d3))
                    b_cnt = b_d1 = b_d2 = b_d3 = 0
            x += steps[s_idx]
            s_idx += 1
            if s_idx == n_off:
                s_idx = 0
        row_end = len(low_x)
        if row_end > row_start:
            low_y_spans.append((y, row_start, row_end))
        if b_cnt > 0:
            blks.append((b_x0, b_xf, b_xl, b_cnt, b_d1, b_d2, b_d3))
        if blks:
            high_by_y2.append((y, y2, blks))
        y += 1
    _RAW_CAND_CACHE[key] = ((low_x, low_y_spans), high_by_y2)
    return _RAW_CAND_CACHE[key]


_Q_DYADIC_MS = 1 << 44


def compute_meixner_schur_var_ub_iv(
    cls,
    R: int,
    S: int,
    K: int,
    eps_num: int,
    eps_den: int,
    eps_lo_iv,
    theta_lo_iv,
    eta_hi_iv,
    L_hi_iv,
    A_num: int = 9,
    A_den: int = 200,
    v_num: int = 93,
    v_den: int = 100,
    beta_num: int = -3,
    beta_den: int = 5,
    dual_num: int = 19,
    dual_den: int = 200,
    nt: int = 128,
    nz: int = 256,
    nm: int = 512,
    kappas_rat: tuple = ((5, 2), (3, 1), (4, 1), (6, 1), (10, 1)),
    rhos_rat: tuple = (
        (1, 100), (3, 100), (3, 50), (1, 10), (3, 20), (1, 5), (3, 10), (2, 5),
        (1, 2), (3, 5), (7, 10), (4, 5), (9, 10), (19, 20), (99, 100), (9999, 10000),
    ),
):
    """
    Self-contained interval enclosure (in FInterval or 26-digit DInterval) of the
    3-branch Node-Block Fischer + Meixner/Composition/Schur variable Archimedean
    upper bound, using the spectral estimates cited in the paper.
    Uses only the Python standard library (fractions, math, decimal).
    """
    from fractions import Fraction as F

    is_dec = (cls is vjd.DInterval)
    q_dec = vjd.Decimal(_Q_DYADIC_MS) if is_dec else None

    def rat(num: int, den: int = 1):
        return cls(num) / cls(den) if den != 1 else cls(num)

    def upper_q(iv) -> int:
        hi_f = float(iv.hi)
        n = math.ceil(hi_f * _Q_DYADIC_MS)
        if is_dec:
            target = iv.hi * q_dec
            while vjd.Decimal(n) < target:
                n += 1
            while vjd.Decimal(n - 1) >= target:
                n -= 1
        else:
            while float(n) / _Q_DYADIC_MS < iv.hi:
                n += 1
        return n

    def xl(x):
        if x.hi <= 0:
            return cls(0)
        return x * x.ln()

    def F2(x):
        return (x * x * x.ln()) / cls(2) - (x * x) / cls(4)

    def F3(x):
        x3 = x * x * x
        return (x3 * x.ln()) / cls(3) - x3 / cls(9)

    def I_fn(x):
        if x.hi <= 0:
            return cls(0)
        return F2(x)

    def iv_abs(x):
        zero = vjd.Decimal(0) if is_dec else 0.0
        if x.lo >= zero:
            return x
        if x.hi <= zero:
            return cls(0) - x
        m = max(-x.lo, x.hi)
        return cls(zero, m)

    eps_hi_f = F(eps_num, eps_den)
    A_f = F(A_num, A_den)
    v_f = F(v_num, v_den)
    beta_f = F(beta_num, beta_den)
    dual_f = F(dual_num, dual_den)
    assert A_f > 0 and 0 < v_f < 1 and beta_f < 0 and dual_f > 0
    assert A_f * R > 1 and R > 3 and eps_hi_f <= 1
    assert A_f <= 1 and eps_hi_f * (A_f + 2 * eps_hi_f) <= 1

    cap = eps_hi_f / nz + F(1, R)
    step = eps_hi_f / nm
    den = math.lcm(cap.denominator, step.denominator)
    cap_units = int(cap * den)
    cap_den = cap_units * den
    step_units = int(step * den)
    step_units_sq = step_units * step_units
    den_sq = den * den
    lo_arr = []
    hi_arr = []
    whole_arr = []
    rem_den_arr = []
    m_sq_arr = [m * m for m in range(nm)]
    for m in range(nm):
        lo = m * step_units
        hi = (m + 1) * step_units
        whole, rem = divmod(hi, cap_units)
        assert whole < nz
        lo_arr.append(lo)
        hi_arr.append(hi)
        whole_arr.append(whole)
        rem_den_arr.append(rem * den)

    Ab = rat(A_num, A_den)
    vb = rat(v_num, v_den)
    bb = rat(beta_num, beta_den)
    eps = rat(eps_num, eps_den)
    eta = eta_hi_iv
    L_iv = L_hi_iv
    R_iv = cls(R)
    S_iv = cls(S)
    K_iv = cls(K)
    one = cls(1)
    two = cls(2)
    three = cls(3)

    dual_units = round(dual_f * _Q_DYADIC_MS)
    dual_iv = rat(dual_units, _Q_DYADIC_MS)

    xl_Ab = xl(Ab)
    ln_vb = vb.ln()
    f1 = cls(0) - xl(Ab + one) + xl_Ab - ln_vb
    assert f1.hi < 0

    integral = (
        cls(0) - rat(5, 36)
        - (Ab + one) * (F2(Ab + one) - F2(Ab))
        + F3(Ab + one) - F3(Ab)
        + xl_Ab / two
        - ln_vb / cls(6)
    )
    C = cls(0) - Ab * (one - vb).ln()
    rowerr = cls(R + 1).ln() + one + ((Ab + one) / (Ab - one / R_iv)).ln()
    row_upper_q = upper_q(
        three * integral
        + cls(9) * C / R_iv
        + (bb / cls(2 * K)) * (one - one / cls(S * S))
        + (three * (one + one / S_iv) / cls(2 * R)) * rowerr
    )

    den_z = eps_den * nz
    two_eps_num_k = [2 * k * eps_num for k in range(nz + 1)]
    z_grid_iv = [rat(k * eps_num, den_z) for k in range(nz + 1)]
    f0 = [0 if k == 0 else upper_q(xl(z_grid_iv[k]) + xl(Ab + z_grid_iv[k]) - xl_Ab) for k in range(nz + 1)]

    schur_cells = []
    for m in range(nm):
        lo, hi = lo_arr[m], hi_arr[m]
        mid_iv = rat(lo + hi, 2 * den)
        t1 = Ab + two * eps - mid_iv
        t2 = Ab + two * eps - two * mid_iv
        b_val = I_fn(mid_iv) + I_fn(t1) - I_fn(t2) - mid_iv * xl_Ab - dual_iv * mid_iv
        b_der = xl(mid_iv) - xl(t1) + two * xl(t2) - xl_Ab - dual_iv
        num_c0_v = 2 * eps_num * (lo + hi) * (2 * den) - eps_den * (lo + hi) * (lo + hi)
        num_c0_d = 2 * (2 * eps_num * den - eps_den * (lo + hi))
        assert num_c0_v >= 0 and num_c0_d >= 0
        schur_cells.append((
            lo + hi,
            hi - lo,
            num_c0_v,
            num_c0_d,
            (lo + hi) * (lo + hi),
            upper_q(b_val),
            upper_q(cls(0) - b_der),
            upper_q(b_der),
        ))

    rhos_info = []
    for rn, rd in rhos_rat:
        r_iv = rat(rn, rd)
        r2_iv = r_iv * r_iv
        omr2_sq = (one - r2_iv) * (one - r2_iv)
        lnr_iv = r_iv.ln()
        rhos_info.append((r_iv, r2_iv, omr2_sq, lnr_iv, upper_q(lnr_iv)))
    kappas_iv = [rat(kn, kd) for kn, kd in kappas_rat]
    n_rhos = len(rhos_info)

    lnR_R = R_iv.ln() / R_iv + (cls(R + 1).ln() + one) / R_iv
    schur_err_q = upper_q((eps * (two * R_iv.ln() + two - eps.ln() - Ab.ln())) / R_iv)
    eps_Ab_eps = eps * (Ab + eps)
    Ab_sq = Ab * Ab

    def build_col_int(slope_iv):
        s_q = upper_q(slope_iv)
        vals = [f0[k] - (-(two_eps_num_k[k] * s_q) // den_z) for k in range(nz + 1)]
        costs = [max(0, vals[k], vals[k + 1]) for k in range(nz)]
        costs.sort(reverse=True)
        cs_cap = [0]
        acc = 0
        for c in costs:
            acc += c * cap_den
            cs_cap.append(acc)
        return [cs_cap[whole_arr[m]] + rem_den_arr[m] * costs[whole_arr[m]] for m in range(nm)]

    def eval_min_quads(q_params):
        res = [0] * nm
        for b0 in range(0, nm, 64):
            b1 = min(nm - 1, b0 + 63)
            bmid = (b0 + b1) >> 1
            bmid2 = bmid * bmid
            best_r = 0
            A0, B0, C0 = q_params[0]
            best_mid = A0 + B0 * bmid + C0 * bmid2
            for r_idx in range(1, n_rhos):
                Ar, Br, Cr = q_params[r_idx]
                vm = Ar + Br * bmid + Cr * bmid2
                if vm < best_mid:
                    best_mid = vm
                    best_r = r_idx
            A0, B0, C0 = q_params[best_r]
            active = []
            b0_sq = b0 * b0
            b1_sq = b1 * b1
            for r_idx in range(n_rhos):
                if r_idx == best_r:
                    continue
                Ar, Br, Cr = q_params[r_idx]
                dA = Ar - A0
                dB = Br - B0
                dC = Cr - C0
                v0 = dA + dB * b0 + dC * b0_sq
                v1 = dA + dB * b1 + dC * b1_sq
                if dC <= 0:
                    if v0 >= 0 and v1 >= 0:
                        continue
                else:
                    if dB + 2 * dC * b0 >= 0 and v0 >= 0:
                        continue
                    if dB + 2 * dC * b1 <= 0 and v1 >= 0:
                        continue
                    if 4 * dC * dA >= dB * dB:
                        continue
                active.append((Ar, Br, Cr))
            if not active:
                for m in range(b0, b1 + 1):
                    res[m] = A0 + B0 * m + C0 * m_sq_arr[m]
            else:
                for m in range(b0, b1 + 1):
                    m2 = m_sq_arr[m]
                    best_v = A0 + B0 * m + C0 * m2
                    for Ar, Br, Cr in active:
                        v = Ar + Br * m + Cr * m2
                        if v < best_v:
                            best_v = v
                    res[m] = best_v
        return res

    Hsum_num = 0
    for i in range(nt):
        if i == nt - 1:
            q = one
        else:
            rt = (cls(i + 1) / cls(nt)).sqrt()
            u = (rt + eta) / (one + eta)
            q = rat(upper_q(u * u), _Q_DYADIC_MS)
        pos_raw = q.ln() - bb
        if pos_raw.hi < 0:
            positive = cls(0)
        elif pos_raw.lo > 0:
            positive = pos_raw
        else:
            positive = rat(upper_q(pos_raw), _Q_DYADIC_MS)
        pos_K = positive / K_iv
        veff = vb * (cls(0) - pos_K).exp()
        vq = veff * q
        om_vq = one - vq
        ln_om_vq = om_vq.ln()
        sqrt_veff = veff.sqrt()
        sqrt_vq = vq.sqrt()

        worst = [None] * nm

        # Branch 1: Infinite Meixner (forward radial generating function)
        for r_iv, r2_iv, omr2_sq, lnr_iv, quad_r in rhos_info:
            G = (one + r2_iv + (omr2_sq + cls(4) * vq * r2_iv).sqrt()) / two
            tau = (r_iv * om_vq) / (G * sqrt_veff)
            slope = L_iv - one - tau.ln()
            col_arr = build_col_int(slope)
            linear = upper_q(Ab * (G / om_vq).ln() + pos_K + lnR_R - lnr_iv / R_iv)
            lin_den = (linear - dual_units) * den
            B_r = lin_den * step_units
            A_r = B_r if lin_den >= 0 else 0
            C_r = quad_r * step_units_sq
            for m in range(nm):
                val = col_arr[m] + A_r + B_r * m + C_r * m_sq_arr[m]
                w_m = worst[m]
                if w_m is None or val < w_m:
                    worst[m] = val

        # Branch 2: Finite Complement (reverse degree-2A+2j Cauchy contour)
        mass_fc = pos_K - Ab * ln_om_vq + lnR_R
        one_p_sqrt_vq = one + sqrt_vq
        for kap_iv in kappas_iv:
            d = kap_iv / one_p_sqrt_vq
            aa = d * sqrt_vq
            aa2_4 = cls(4) * aa * aa
            tau = (d * om_vq) / sqrt_veff
            slope = L_iv - one - tau.ln()
            col_arr = build_col_int(slope)
            lnd = d.ln()
            abs_lnd = iv_abs(lnd)
            mass_err = mass_fc + (abs_lnd - lnd) / cls(2 * R)

            q_params = []
            for r_iv, r2_iv, omr2_sq, lnr_iv, _ in rhos_info:
                G = (one + r2_iv + (omr2_sq + aa2_4 * r2_iv).sqrt()) / two
                lng = G.ln()
                lnsig = lnd + lnr_iv - lng
                abs_lnsig = iv_abs(lnsig)
                const_term = upper_q(eps_Ab_eps * lng) * den_sq
                linear = upper_q(mass_err - Ab * lng - eps * (two * lnr_iv - lnsig - abs_lnsig))
                quad = upper_q(lnr_iv - abs_lnsig)
                assert quad < 0
                lin_den = (linear - dual_units) * den
                B_r = lin_den * step_units
                A_r = const_term + (B_r if lin_den >= 0 else 0)
                C_r = quad * step_units_sq
                q_params.append((A_r, B_r, C_r))

            min_q = eval_min_quads(q_params)
            for m in range(nm):
                val = col_arr[m] + min_q[m]
                if val < worst[m]:
                    worst[m] = val

        # Branch 3: Weighted Schur Row-Sum Bound
        c0 = L_iv + veff.ln() / two - ln_om_vq
        zz = (cls(0) - two * c0).exp() / Ab_sq
        assert c0.lo > 0 and zz.lo > 0 and zz.hi < 1
        assert (eps_Ab_eps * zz).hi < (Ab_sq * (one - zz) * (one - zz)).lo
        mass_s = pos_K - Ab * ln_om_vq
        ln_1mzz = (one - zz).ln()
        c0_m1 = c0 - one
        mass_hi_q = upper_q(mass_s)
        mass_mlo_q = upper_q(cls(0) - mass_s)
        c0m1_hi_q = upper_q(c0_m1)
        c0m1_mlo_q = upper_q(cls(0) - c0_m1)
        mln1mzz_hi_q = upper_q(cls(0) - ln_1mzz)
        mln1mzz_mlo_q = upper_q(ln_1mzz)
        den2_4_eps = 4 * eps_den * den_sq
        den_2_eps = 2 * eps_den * den
        den2_4 = 4 * den_sq
        den_2 = 2 * den
        for m, (mid_2d, wid_2d, num_c0_v, num_c0_d, mid_sq_4d2, b_val_q, mb_der_lo_q, b_der_hi_q) in enumerate(schur_cells):
            v_q = (
                b_val_q
                - (-(mid_2d * mass_hi_q) // den_2)
                - (-(num_c0_v * c0m1_hi_q) // den2_4_eps)
                - (-(mid_sq_4d2 * mln1mzz_hi_q) // den2_4)
            )
            d_hi_q = (
                b_der_hi_q
                + mass_hi_q
                - (-(num_c0_d * c0m1_hi_q) // den_2_eps)
                - (-(2 * mid_2d * mln1mzz_hi_q) // den_2)
            )
            md_lo_q = (
                mb_der_lo_q
                + mass_mlo_q
                - (-(num_c0_d * c0m1_mlo_q) // den_2_eps)
                - (-(2 * mid_2d * mln1mzz_mlo_q) // den_2)
            )
            abs_d_q = d_hi_q if d_hi_q >= md_lo_q else md_lo_q
            if abs_d_q < 0:
                abs_d_q = 0
            bnd_q = v_q - (-(abs_d_q * wid_2d) // den_2) + schur_err_q
            cand = bnd_q * den_sq
            if cand < worst[m]:
                worst[m] = cand

        Hsum_num += max(0, max(worst))

    row_upper_iv = rat(row_upper_q, _Q_DYADIC_MS)
    Hsum_iv = rat(Hsum_num, _Q_DYADIC_MS * den_sq)
    nodefactor = three * ((one + one / S_iv) / (two * theta_lo_iv * eps_lo_iv * cls(nt)) + one / S_iv)
    dualcharge = rat(3, 2) * dual_iv * (one + one / S_iv)
    return row_upper_iv + dualcharge + nodefactor * Hsum_iv


def compute_charlier_var_ub_iv(
    cls,
    R: int,
    S: int,
    K: int,
    J: int,
    n: int,
    eta_iv,
    L_iv,
    a_num: int = 27,
    a_den: int = 50,
    beta_num: int = -9,
    beta_den: int = 10,
):
    """
    Closed-form Charlier/Poisson complement bound (unused in this release)
    for (log |det B_C|^2) / W_main with zero spectral or row grids.
    """
    M_tri = R * (S + 1) // 2
    q_miss = n * J - M_tri
    assert q_miss >= 0 and R == K * S

    i0, i1, i2, i3, i4, _, _, _ = _consts(cls)
    i6, i9, i11, i12 = cls(6), cls(9), cls(11), cls(12)
    iR, iS, iK, iJ, in_val, iq = cls(R), cls(S), cls(K), cls(J), cls(n), cls(q_miss)
    a = cls(a_num) / cls(a_den)
    beta = cls(beta_num) / cls(beta_den)
    assert float((a * i1.exp()).lo) >= 1.0 and float(beta.hi) < 0.0

    u = beta.exp()
    sqrt_u = (beta / i2).exp()
    q0_rt = eta_iv / (i1 + eta_iv)
    q0 = q0_rt * q0_rt
    assert float(q0.hi) < float(u.lo)

    # Monotonicity guard (8.11): K * exp(-L) + exp(-2*L - beta/K) / a <= 1
    guard = iK * (i0 - L_iv).exp() + (i0 - i2 * L_iv - beta / iK).exp() / a
    assert float(guard.hi) <= 1.0

    eps = iJ / iR
    eps_m_1R = (iJ - i1) / iR
    ln_eps = eps.ln()
    ln_Rp1 = cls(R + 1).ln()
    ln_S_R = iS.ln() / iR
    ln_a = a.ln()

    U_row = (
        (i0 - i11 / i12)
        - ln_a / i2
        + (i9 * a) / iR
        + (beta / (i2 * iK)) * (i1 - i1 / (iS * iS))
        + (i3 * (i1 + i1 / iS) / (i2 * iR)) * (ln_Rp1 + i1)
    )

    A_eta = (i1 + eta_iv) * (i1 + eta_iv)
    B_eta = eta_iv * (i1 + eta_iv)
    delta_bar = A_eta * (i0 - beta - i1 + u) - B_eta * (i0 - i2 * beta - i4 + i4 * sqrt_u)

    p_exp = i2 - i1 / iK
    r_exp = cls(3) / i2 - i1 / iK
    eb_K = (beta / iK).exp()
    u_p = (beta * p_exp).exp()
    u_r = (beta * r_exp).exp()
    T_bar = (
        A_eta * ((u * u - q0 * q0) / i2 + eb_K * (i1 - u_p) / p_exp)
        - B_eta * ((i2 / i3) * (u * sqrt_u - q0 * q0_rt) + eb_K * (i1 - u_r) / r_exp)
    )

    c_delta = (eps / iK) * (i1 - eps_m_1R / i2)
    assert float(c_delta.lo) > 0.0

    D_const = (
        eps * ln_S_R
        + (eps * eps * ln_eps) / i2
        - (i3 * eps * eps) / i4
        + (eps * eps_m_1R / i2) * (i2 * L_iv + ln_a)
        + (eps / iR) * (i2 - ln_eps + ln_Rp1)
    )
    D_bar = D_const + c_delta * delta_bar + eps * a * T_bar
    Delta_D = c_delta * (i0 - beta) + eps * a * (eb_K - q0)
    vol_term = (i3 / iS) * (in_val * D_bar + Delta_D)

    kappa = (i0 - ln_S_R) + (i0 - i2 * L_iv).exp() / a + i2 * (i0 - L_iv + beta / i2).exp()
    omitted_term = (i3 * iq / (iR * iS)) * kappa

    return U_row + vol_term + omitted_term


_DF_RANK_CACHE: dict = {}


def verify_divided_frobenius_rank_window(
    D_lo: int,
    D_hi: int,
    K: int,
    S: int,
    R: int,
    J: int,
    A_df: int,
    B_df: int,
    cls=vjd.FInterval,
    M_steps: int = 800,
):
    """
    Self-contained interval-arithmetic and exact integer verifier for Lemma 3.5
    (Mixed Divided-Frobenius Full-Rank Criterion and Inert-Prime Annular Window;
    the exact rank criterion and prime-window count in the paper).
    """
    key = (K, S, R, J, A_df, B_df, M_steps)
    if key in _DF_RANK_CACHE:
        n, n_primes, total_ineqs, min_margin = _DF_RANK_CACHE[key]
    else:
        assert K < A_df < B_df and R <= A_df * A_df and 1 <= J <= R
        if vjd.PRIMES[-1] < B_df:
            vjd.PRIMES = vjd.sieve_primes(B_df + 1000)
        i0 = bisect.bisect_right(vjd.PRIMES, A_df)
        i1 = bisect.bisect_right(vjd.PRIMES, B_df)
        primes_ab = vjd.PRIMES[i0:i1]
        n_primes = len(primes_ab)
        assert n_primes > 0
        req_n = 2 * S
        total_ineqs = 0
        for p_idx, p in enumerate(primes_ab):
            d = (R - 1) // p
            assert d < p
            Q = J // p
            r_j = J - Q * p
            B_e = 0
            for e in range(d + 1):
                rem = R - e * p - 1
                q_k, r_k = divmod(rem, K)
                B_e += p * q_k + r_k - e
                if e < Q:
                    mu_e = (e + 1) * p - (e * (e + 1)) // 2
                elif e >= Q + p:
                    mu_e = J
                else:
                    l_start = max(0, e - p + 1)
                    cnt_full = Q - l_start
                    mu_e = cnt_full * (p - e) + ((Q - 1 + l_start) * cnt_full) // 2
                    if r_j - e + Q > 0:
                        mu_e += r_j - e + Q
                if p_idx == 0 and e <= min(d, Q + 5):
                    mu_direct = sum(max(0, min(p, max(0, J - l_idx * p)) - e + l_idx) for l_idx in range(e + 1))
                    assert mu_e == mu_direct
                n_e = (B_e // mu_e) + 1
                if n_e > req_n:
                    req_n = n_e
            total_ineqs += (d + 1)
        n = ((req_n + M_steps - 1) // M_steps) * M_steps
        min_margin = None
        for p in primes_ab:
            d = (R - 1) // p
            Q = J // p
            r_j = J - Q * p
            B_e = 0
            for e in range(d + 1):
                rem = R - e * p - 1
                q_k, r_k = divmod(rem, K)
                B_e += p * q_k + r_k - e
                if e < Q:
                    mu_e = (e + 1) * p - (e * (e + 1)) // 2
                elif e >= Q + p:
                    mu_e = J
                else:
                    l_start = max(0, e - p + 1)
                    cnt_full = Q - l_start
                    mu_e = cnt_full * (p - e) + ((Q - 1 + l_start) * cnt_full) // 2
                    if r_j - e + Q > 0:
                        mu_e += r_j - e + Q
                marg = n * mu_e - B_e
                assert marg > 0
                if min_margin is None or marg < min_margin:
                    min_margin = marg
        _DF_RANK_CACHE[key] = (n, n_primes, total_ineqs, min_margin)

    assert D_hi <= A_df
    iv_0, iv_1, iv_2, iv_4 = cls(0), cls(1), cls(2), cls(4)
    pi_iv = (
        cls(vjd.Decimal("3.14159265358979323846264338"), vjd.Decimal("3.14159265358979323846264339"))
        if cls is vjd.DInterval
        else vjd.FInterval(math.pi)
    )
    delta_D_hi_iv = cls(D_hi + 4).sqrt() / iv_4
    base_rad_hi_iv = ((cls(n) * cls(D_hi).sqrt()) / (iv_2 * pi_iv)).sqrt()
    rho_n_hi_iv = base_rad_hi_iv + delta_D_hi_iv
    diam_hi = iv_2 * rho_n_hi_iv
    assert float(diam_hi.hi) < A_df

    y_max = int(math.isqrt((4 * B_df) // D_lo))
    assert A_df >= 4 and D_lo * (y_max + 1) * (y_max + 1) > 4 * B_df
    A_iv, B_iv = cls(A_df), cls(B_df)
    D_lo_iv, D_hi_iv = cls(D_lo), cls(D_hi)
    split_ub = iv_0
    for y in range(1, y_max + 1):
        y2_iv = cls(y * y)
        hi_rad = (B_iv - (D_lo_iv * y2_iv) / iv_4).sqrt()
        lo_arg = A_iv - (D_hi_iv * y2_iv) / iv_4
        lo_rad = lo_arg.sqrt() if lo_arg.hi > 0 else iv_0
        if lo_arg.lo <= 0 < lo_arg.hi:
            lo_rad = cls(0, lo_rad.hi)
        du = hi_rad - lo_rad
        split_ub = split_ub + iv_1 + (du / iv_2 if (y & 1) == 0 else du)
    assert float(split_ub.hi) < n_primes
    return n, n_primes, total_ineqs, min_margin, float(diam_hi.hi), float(split_ub.hi)


def certify_hybrid_k3_interval(
    D_lo: int,
    D_hi: int,
    P_max: int = 8999999,
    K: int = 23,
    c_R_num: int = 14,
    eps_J_num: int = 56,
    Q_guar: int = 750000,
    b0_frac: float = 0.48,
    cls=vjd.FInterval,
    M_min_cache: int | None = None,
    use_k4: bool | None = None,
    clamp_m3: bool | None = None,
    discrete_comp2: bool = True,
    use_meixner_schur: bool = False,
    use_wronskian: bool | tuple = False,
    ms_params: tuple | None = None,
):
    if M_min_cache is None:
        M_min_cache = 153 if P_max >= 500000000 else (170 if P_max >= 200000000 else (175 if P_max >= 100000000 else (178 if P_max >= 50000000 else 185)))
    if use_k4 is None:
        use_k4 = (P_max >= 500000000)
    if clamp_m3 is None:
        clamp_m3 = not (P_max >= 500000000)
    assert D_lo % 4 == 3 and D_hi % 4 == 3 and D_lo <= D_hi
    M_steps = 800
    S = max(10, (c_R_num * P_max) // (10 * K))
    R = K * S
    J = max(2, (eps_J_num * R) // 1000)
    ensure_tables_up_to(P_max, J)
    M_tri = R * (S + 1) // 2
    W_1 = (R * R * (S + 1) * (2 * S + 1)) // (6 * S) - M_tri
    W_2 = (R * (S * S - 1)) // 3
    delta_D_hi_flt = math.sqrt(D_hi + 4.0) / 4.0
    if isinstance(use_wronskian, tuple):
        A_df, B_df = use_wronskian
        n, _, _, _, _, _ = verify_divided_frobenius_rank_window(D_lo, D_hi, K, S, R, J, A_df, B_df, cls=cls, M_steps=M_steps)
        assert n >= 2 * S and M_tri < n * J
    elif use_wronskian:
        assert J >= S and 2 * (J + 1) <= (K + 1) * S
        n = max(S, ((K - 1) * S * (S + 1)) // (2 * (J - S + 1)) + 1)
        n = ((n + M_steps - 1) // M_steps) * M_steps
        assert n >= S and n * (J - S + 1) > M_tri - (S * (S + 1)) // 2
        assert M_tri < n * J
    else:
        n = (R * S) // J + 1
        for _ in range(30):
            rho_n_hi_flt = math.sqrt(n * math.sqrt(D_hi) / (2.0 * math.pi)) + delta_D_hi_flt
            M_y_hi = 2 * int(2.0 * rho_n_hi_flt / math.sqrt(D_lo)) + 1
            M_x_hi = int(2.0 * rho_n_hi_flt) + 1
            assert max(J, M_x_hi) <= R + M_y_hi * K
            n_req = (R * S + M_y_hi * R) // J + 1
            if n >= n_req:
                break
            n = n_req
        n = ((n + M_steps - 1) // M_steps) * M_steps
    m_bin = n // M_steps
    N_num, D_den = M_tri, m_bin * J

    X_lo = (D_lo - 3) // 4
    M_lo = (D_lo + 1) // 4
    M_hi = (D_hi + 1) // 4
    dM = M_hi - M_lo

    max_factor = min(P_max // M_lo, (M_lo ** 3) - 1) if clamp_m3 else (P_max // M_lo)
    if not use_wronskian:
        assert max_factor < (M_lo ** 4)
    q_cap = min(Q_guar, (M_lo * (M_lo - dM)) ** 2 - 1, J - 1, max_factor * M_lo)
    sf_max = q_cap // M_lo
    assert sf_max <= max_factor
    comp2_bound = max_factor + dM * ((4 * max_factor) // D_lo)
    tier1_bound = comp2_bound // M_lo
    q_cols_c = M_tri // n

    M_cache_key = min(M_lo, M_min_cache)
    assert (J > q_cols_c if use_wronskian else S >= q_cols_c)
    low_cut_cache = max(Q_guar, J - 1, P_max // M_cache_key, comp2_bound, S, q_cols_c)
    (low_x, low_y_spans), high_by_y2 = get_raw_cands_cached(M_cache_key, P_max, low_cut_cache)

    iv_0, iv_1, iv_2, iv_3, iv_4 = cls(0), cls(1), cls(2), cls(3), cls(4)
    iv_K, iv_S, iv_R, iv_J, iv_M, iv_M_tri = cls(K), cls(S), cls(R), cls(J), cls(M_steps), cls(M_tri)
    W_main_iv = cls(R * R * S) / iv_3
    W2_norm_iv = cls(W_2) / W_main_iv
    W12_norm_iv = cls(W_1 + W_2) / W_main_iv
    pi_iv = (
        cls(vjd.Decimal("3.14159265358979323846264338"), vjd.Decimal("3.14159265358979323846264339"))
        if cls is vjd.DInterval
        else vjd.FInterval(math.pi)
    )
    W_main_f = vjd.FInterval(R * R * S) / vjd.FInterval(3)
    inv_KWm_f = vjd.FInterval(1) / (vjd.FInterval(K) * W_main_f)
    RRK = R * (R + K)
    RK2 = 2 * R + K
    inv_KWm_hi = inv_KWm_f.hi
    inv_KWm_lo = inv_KWm_f.lo
    wm_lo = W_main_f.lo
    wm_hi = W_main_f.hi

    def loss_ub_flt(p_lo: int, p_hi: int, in_slope: bool, lp_lo_cached: float) -> float:
        log_lo_hi = vjd._ln_hi_only(float(p_lo))
        q = R // p_lo
        sr_ub = q * RRK - ((q * (q + 1)) >> 1) * RK2 * p_lo + ((q * (q + 1) * (2 * q + 1)) // 6) * p_lo * p_lo
        wr_log_ub = _NA(_NA(_NA(float(sr_ub), _INF) * inv_KWm_hi, _INF) * log_lo_hi, _INF)
        if p_hi > S and (in_slope or p_hi > q_cols_c):
            return wr_log_ub
        log_lo_lo = lp_lo_cached if lp_lo_cached > 0.0 else vjd._ln_lo_only(float(p_lo))
        s_gain_lb = 0.0
        if p_hi <= S:
            sum_s_lb = 0
            p_pow_hi = p_hi
            while p_pow_hi <= S:
                sum_s_lb += vjd.sum_floor_s_tri(S, p_pow_hi)
                p_pow_hi *= (p_hi * p_hi)
            if sum_s_lb > 0:
                s_gain_lb = _NA(float(2 * K * sum_s_lb) / wm_hi, _NINF)
        c_save_lb = 0.0
        if not in_slope and p_hi <= q_cols_c:
            tf_lb = vjd.col_split_floor_total(p_hi, n, M_tri)
            if tf_lb > 0:
                c_save_lb = _NA(_NA(float(2 * tf_lb) / wm_hi, _NINF) * log_lo_lo, _NINF)
        return max(0.0, _NA(_NA(wr_log_ub - _NA(s_gain_lb * log_lo_lo, _NINF), _INF) - c_save_lb, _INF))

    def loss_lb_flt(p_lo: int, p_hi: int, in_slope: bool) -> float:
        log_hi_lo = vjd._ln_lo_only(float(p_hi))
        q = R // p_hi
        sr_lb = q * RRK - ((q * (q + 1)) >> 1) * RK2 * p_hi + ((q * (q + 1) * (2 * q + 1)) // 6) * p_hi * p_hi
        wr_log_lb = _NA(_NA(_NA(float(sr_lb), _NINF) * inv_KWm_lo, _NINF) * log_hi_lo, _NINF)
        if p_lo > S and (in_slope or p_lo > q_cols_c):
            return wr_log_lb
        log_hi_hi = vjd._ln_hi_only(float(p_hi))
        s_gain_ub = 0.0
        if p_lo <= S:
            sum_s_ub = 0
            p_pow_lo = p_lo
            while p_pow_lo <= S:
                sum_s_ub += vjd.sum_floor_s_tri(S, p_pow_lo)
                p_pow_lo *= (p_lo * p_lo)
            if sum_s_ub > 0:
                s_gain_ub = _NA(float(2 * K * sum_s_ub) / wm_lo, _INF)
        c_save_ub = 0.0
        if not in_slope and p_lo <= q_cols_c:
            tf_ub = vjd.col_split_floor_total(p_lo, n, M_tri)
            if tf_ub > 0:
                c_save_ub = _NA(_NA(float(2 * tf_ub) / wm_lo, _INF) * log_hi_hi, _INF)
        return max(0.0, _NA(_NA(wr_log_lb - _NA(s_gain_ub * log_hi_hi, _INF), _NINF) - c_save_ub, _NINF))

    use_flt_sigma2 = (cls is vjd.FInterval or q_cap > 3600000)
    sieve_flt_key = ("sieve_flt", D_lo, D_hi, P_max, K, c_R_num, eps_J_num, Q_guar, use_k4, clamp_m3, discrete_comp2, M_cache_key, n)
    if use_flt_sigma2 and sieve_flt_key in vjd._HYBRID_PADIC_CACHE:
        (s_lo_flt, s_hi_flt, tot_H_ub, split_loss_hi, ufd_save_lo, save_k2, save_k3, save_k4, G1, G, n_comp_total) = vjd._HYBRID_PADIC_CACHE[sieve_flt_key]
        sigma2_lo_iv = cls(s_lo_flt, s_lo_flt)
        sigma2_hi_iv = cls(s_hi_flt, s_hi_flt)
        delta_D_lo_iv = cls(D_lo + 4).sqrt() / iv_4
        delta_D_hi_iv = cls(D_hi + 4).sqrt() / iv_4
        base_rad_lo_iv = ((cls(n) * cls(D_lo).sqrt()) / (iv_2 * pi_iv)).sqrt()
        base_rad_hi_iv = ((cls(n) * cls(D_hi).sqrt()) / (iv_2 * pi_iv)).sqrt()
        rho_n_lo_iv = base_rad_lo_iv + delta_D_lo_iv
        rho_n_hi_iv = base_rad_hi_iv + delta_D_hi_iv
        theta_iv = cls(M_tri) / cls(n * J)
        actual_eps_J_iv = iv_J / iv_R
        slope_j_lo_iv = (iv_R / rho_n_hi_iv).ln() - sigma2_hi_iv
        slope_j_hi_iv = (iv_R / rho_n_lo_iv).ln() - sigma2_lo_iv
    else:
        tier1_cands = []
        for y, r_start, r_end in low_y_spans:
            y2 = y * y
            m_lo_y2 = M_lo * y2
            if m_lo_y2 - (y2 >> 2) > tier1_bound:
                break
            m_hi_y2 = M_hi * y2
            for idx_r in range(r_start, r_end):
                x = low_x[idx_r]
                x2_xy = x * (x + y)
                p_lo_raw = x2_xy + m_lo_y2
                if p_lo_raw <= tier1_bound:
                    is_ram = (y == 2 and x == -1)
                    p_hi_raw = x2_xy + m_hi_y2
                    tier1_cands.append((p_lo_raw, p_hi_raw, is_ram, x, y))
        tier1_cands.sort()
        G1 = len(tier1_cands)

        # 2D compact bitmap for comp2 (replaces 180 MB dict of interval lists with < 1 MB bytearray)
        Y_max = int((4 * comp2_bound / D_lo) ** 0.5) + 2
        U_max = int((4 * comp2_bound) ** 0.5) + 2
        stride = U_max + 1
        comp2_grid = bytearray((Y_max + 1) * stride)

        for i in range(G1):
            p1_lo, p1_hi, ram1, x1, y1 = tier1_cands[i]
            if p1_lo * p1_lo > comp2_bound:
                break
            u1 = 2 * x1 + y1
            for j in range(i, G1):
                p2_lo, p2_hi, ram2, x2, y2 = tier1_cands[j]
                if p1_lo * p2_lo > comp2_bound:
                    break
                if i == j and ram1:
                    continue
                u2 = 2 * x2 + y2
                yp = (u1 * y2 + u2 * y1) // 2
                if yp <= Y_max:
                    row = yp * stride
                    if discrete_comp2:
                        if dM == 0:
                            up_0 = abs(u1 * u2 - D_lo * y1 * y2) // 2
                            if up_0 <= U_max:
                                comp2_grid[row + up_0] = 1
                        elif dM == 1:
                            u1u2 = u1 * u2
                            y1y2 = y1 * y2
                            up_0 = abs(u1u2 - D_lo * y1y2) // 2
                            if up_0 <= U_max:
                                comp2_grid[row + up_0] = 1
                            up_1 = abs(u1u2 - D_hi * y1y2) // 2
                            if up_1 <= U_max:
                                comp2_grid[row + up_1] = 1
                        else:
                            u1u2 = u1 * u2
                            y1y2 = y1 * y2
                            for m_step in range(dM + 1):
                                dm = D_lo + 4 * m_step
                                up_m = abs(u1u2 - dm * y1y2) // 2
                                if up_m <= U_max:
                                    comp2_grid[row + up_m] = 1
                    else:
                        f_lo = (u1 * u2 - D_hi * y1 * y2) // 2
                        f_hi = (u1 * u2 - D_lo * y1 * y2) // 2
                        up_lo = 0 if (f_lo <= 0 <= f_hi) else min(abs(f_lo), abs(f_hi))
                        if up_lo <= U_max:
                            up_hi = min(U_max, max(abs(f_lo), abs(f_hi)))
                            if up_lo == up_hi:
                                comp2_grid[row + up_lo] = 1
                            else:
                                comp2_grid[row + up_lo : row + up_hi + 1] = b"\x01" * (up_hi - up_lo + 1)
                if i != j and not (ram1 or ram2):
                    ym = abs(u2 * y1 - u1 * y2) // 2
                    if ym <= Y_max:
                        row = ym * stride
                        if discrete_comp2:
                            if dM == 0:
                                um_0 = (u1 * u2 + D_lo * y1 * y2) // 2
                                if um_0 <= U_max:
                                    comp2_grid[row + um_0] = 1
                            elif dM == 1:
                                u1u2 = u1 * u2
                                y1y2 = y1 * y2
                                um_0 = (u1u2 + D_lo * y1y2) // 2
                                if um_0 <= U_max:
                                    comp2_grid[row + um_0] = 1
                                um_1 = (u1u2 + D_hi * y1y2) // 2
                                if um_1 <= U_max:
                                    comp2_grid[row + um_1] = 1
                            else:
                                u1u2 = u1 * u2
                                y1y2 = y1 * y2
                                for m_step in range(dM + 1):
                                    dm = D_lo + 4 * m_step
                                    um_m = (u1u2 + dm * y1y2) // 2
                                    if um_m <= U_max:
                                        comp2_grid[row + um_m] = 1
                        else:
                            um_lo = (u1 * u2 + D_lo * y1 * y2) // 2
                            if um_lo <= U_max:
                                um_hi = min(U_max, (u1 * u2 + D_hi * y1 * y2) // 2)
                                if um_lo == um_hi:
                                    comp2_grid[row + um_lo] = 1
                                else:
                                    comp2_grid[row + um_lo : row + um_hi + 1] = b"\x01" * (um_hi - um_lo + 1)
        del tier1_cands

        sigma2_pp_f = vjd.FInterval(0)
        for p in vjd.PRIMES:
            pk = p * p
            if pk > J - 1:
                break
            lp_f = vjd.FInterval(p).ln()
            while pk <= J - 1:
                sigma2_pp_f = sigma2_pp_f + lp_f / vjd.FInterval(pk)
                pk *= p
        use_flt_sigma2 = (cls is vjd.FInterval or q_cap > 3600000)
        if use_flt_sigma2:
            sigma2_pp_iv = cls(sigma2_pp_f.lo, sigma2_pp_f.hi)
        else:
            sigma2_pp_iv = iv_0
            for p in vjd.PRIMES:
                pk = p * p
                if pk > J - 1:
                    break
                lp_iv = cls(p).ln()
                while pk <= J - 1:
                    sigma2_pp_iv = sigma2_pp_iv + lp_iv / cls(pk)
                    pk *= p
        s_lo_flt = sigma2_pp_f.lo
        s_hi_flt = sigma2_pp_f.hi
        sigma2_lo_iv = sigma2_pp_iv
        sigma2_hi_iv = sigma2_pp_iv

        n_blk_j = (J + 31) >> 5
        diff_blk_lo = array.array("d", [0.0]) * (n_blk_j + 1)

        raw_g_lo = array.array("I")
        raw_g_hi = array.array("I") if dM > 0 else None
        raw_g_ram = bytearray() if dM > 0 else None
        extra_sf_cands = []
        split_loss_hi = 0.0

        m_lo_sq = M_lo * M_lo
        for y, r_start, r_end in low_y_spans:
            y2 = y * y
            m_lo_y2 = M_lo * y2
            m_hi_y2 = M_hi * y2
            y_row = y * stride
            for idx_r in range(r_start, r_end):
                x = low_x[idx_r]
                x2_xy = x * (x + y)
                is_ram = (y == 2 and x == -1)
                p_lo_raw = x2_xy + m_lo_y2
                p_hi_raw = x2_xy + m_hi_y2
                if p_lo_raw <= max_factor:
                    u = 2 * x + y
                    if p_lo_raw < m_lo_sq or not comp2_grid[y_row + u]:
                        if dM == 0:
                            raw_g_lo.append((p_lo_raw << 1) | (1 if is_ram else 0))
                        else:
                            raw_g_lo.append(p_lo_raw)
                            raw_g_hi.append(p_hi_raw)
                            raw_g_ram.append(1 if is_ram else 0)
                    elif dM > 0 and p_lo_raw <= sf_max:
                        extra_sf_cands.append((p_lo_raw, p_hi_raw, is_ram))

                if p_lo_raw > P_max:
                    continue
                p_lo = max(X_lo + 1, p_lo_raw)
                p_hi = min(P_max, max(p_lo, p_hi_raw))
                in_slope = (p_hi_raw <= q_cap and p_lo_raw > X_lo and not is_ram)
                lp_lo_cached = vjd._ln_lo_only(float(p_lo)) if (in_slope or p_hi <= S or p_hi <= q_cols_c or is_ram) else 0.0
                if in_slope:
                    if use_flt_sigma2:
                        lp_hi = vjd._ln_hi_only(float(p_hi))
                        s_lo_flt = _NA(s_lo_flt + _NA(lp_lo_cached / float(p_hi), _NINF), _NINF)
                        s_hi_flt = _NA(s_hi_flt + _NA(lp_hi / float(p_lo), _INF), _INF)
                    else:
                        sigma2_lo_iv = sigma2_lo_iv + cls(p_lo).ln() / cls(p_hi)
                        sigma2_hi_iv = sigma2_hi_iv + cls(p_hi).ln() / cls(p_lo)
                    for m in range(p_hi, J, p_hi):
                        idx_b = (m + 31) >> 5
                        if idx_b <= n_blk_j:
                            diff_blk_lo[idx_b] = _NA(diff_blk_lo[idx_b] + lp_lo_cached, _NINF)
                if is_ram:
                    log_lo_lo = lp_lo_cached if lp_lo_cached > 0.0 else vjd._ln_lo_only(float(p_lo))
                    log_lo_hi = vjd._ln_hi_only(float(p_lo))
                    log_hi_hi = vjd._ln_hi_only(float(p_hi))
                    sr_ub = vjd.S_r_exact(R, K, p_lo)
                    wr_log_ub = _NA(_NA(float(sr_ub) * inv_KWm_hi, _INF) * log_lo_hi, _INF)
                    sum_s2 = 0
                    p_pow = p_lo * p_lo
                    while p_pow <= S:
                        sum_s2 += vjd.sum_floor_s_tri(S, p_pow)
                        p_pow *= (p_lo * p_lo)
                    w_s2 = _NA(float(2 * K * sum_s2) / wm_lo, _INF) if sum_s2 > 0 else 0.0
                    tf_lb = vjd.col_split_floor_total(p_hi, n, M_tri)
                    c_save_lb = _NA(_NA(float(2 * tf_lb) / wm_hi, _NINF) * log_lo_lo, _NINF) if tf_lb > 0 else 0.0
                    ram_ub = max(0.0, _NA(0.5 * max(0.0, _NA(_NA(wr_log_ub + _NA(w_s2 * log_hi_hi, _INF), _INF) - c_save_lb, _INF)), _INF))
                    split_loss_hi = _NA(split_loss_hi + ram_ub, _INF)
                else:
                    ub_val = loss_ub_flt(p_lo, p_hi, in_slope, lp_lo_cached)
                    split_loss_hi = _NA(split_loss_hi + ub_val, _INF)

        del comp2_grid
        extra_sf_cands.sort()
        G = len(raw_g_lo)
        # Sort by upper endpoint guar_p_hi ascending so guar_p_hi is monotonically non-decreasing,
        # and precompute the monotonically non-decreasing suffix minimum suf_min_lo of guar_p_lo
        if dM == 0:
            guar_packed = sorted(raw_g_lo)
            del raw_g_lo
            guar_p_lo = array.array("I", (v >> 1 for v in guar_packed))
            guar_ram = bytearray(v & 1 for v in guar_packed)
            del guar_packed
            guar_p_hi = guar_p_lo
            suf_min_lo = guar_p_lo
        else:
            order = sorted(range(G), key=lambda idx: (raw_g_hi[idx] << 31) | (raw_g_lo[idx] << 1) | raw_g_ram[idx])
            guar_p_lo = array.array("I", (raw_g_lo[idx] for idx in order))
            guar_p_hi = array.array("I", (raw_g_hi[idx] for idx in order))
            guar_ram = bytearray(raw_g_ram[idx] for idx in order)
            del raw_g_lo, raw_g_hi, raw_g_ram, order

            suf_min_lo = array.array("I", [0]) * G
            if G > 0:
                cur_min = guar_p_lo[G - 1]
                suf_min_lo[G - 1] = cur_min
                for idx_g in range(G - 2, -1, -1):
                    v_lo = guar_p_lo[idx_g]
                    if v_lo < cur_min:
                        cur_min = v_lo
                    suf_min_lo[idx_g] = cur_min
                for idx_g in range(G - 1):
                    assert guar_p_hi[idx_g] <= guar_p_hi[idx_g + 1]
                    assert suf_min_lo[idx_g] <= suf_min_lo[idx_g + 1]
                    assert suf_min_lo[idx_g] <= guar_p_lo[idx_g] <= guar_p_hi[idx_g]

        ram_idx = -1
        for idx_g, is_r in enumerate(guar_ram):
            if is_r:
                ram_idx = idx_g
                break

        P1 = array.array("Q", [0]) * (G + 1)
        P2_16 = [0] * ((G >> 4) + 2)
        P3_16 = [0] * ((G >> 4) + 2)
        a1 = a2 = a3 = 0
        for idx_g, ph in enumerate(guar_p_hi):
            a1 += ph
            ph2 = ph * ph
            a2 += ph2
            a3 += ph2 * ph
            idx1 = idx_g + 1
            P1[idx1] = a1
            if (idx1 & 15) == 0:
                idx16 = idx1 >> 4
                P2_16[idx16] = a2
                P3_16[idx16] = a3

        def p23_at(idx: int) -> tuple[int, int]:
            base = idx & ~15
            s2 = P2_16[base >> 4]
            s3 = P3_16[base >> 4]
            for k_idx in range(base, idx):
                ph_v = guar_p_hi[k_idx]
                ph2_v = ph_v * ph_v
                s2 += ph2_v
                s3 += ph2_v * ph_v
            return s2, s3

        high_cut_s = max(S, q_cols_c, q_cap)

        def sum_tail_blocks_flt(r_start: int, r_end: int, m_pref_hi: int, mult_const: int) -> float:
            save_blk = 0.0
            r_q_start = r_start
            mh1 = mult_const * m_pref_hi
            mh2 = mh1 * m_pref_hi
            mh3 = mh2 * m_pref_hi
            while r_q_start < r_end:
                q = R // (m_pref_hi * guar_p_hi[r_q_start])
                if q <= 0:
                    break
                max_p_q = (R // q) // m_pref_hi
                r_q = bisect.bisect_right(guar_p_hi, max_p_q, r_q_start, r_end)
                Aq = q * RRK
                Bq = ((q * (q + 1)) >> 1) * RK2
                Cq = (q * (q + 1) * (2 * q + 1)) // 6
                p2_r0, p3_r0 = p23_at(r_q_start)
                for r0 in range(r_q_start, r_q, 16):
                    r1 = r0 + 16
                    if r1 > r_q:
                        r1 = r_q
                    p2_r1, p3_r1 = p23_at(r1)
                    m_a = m_pref_hi * guar_p_hi[r0]
                    m_b = m_pref_hi * guar_p_hi[r1 - 1]
                    assert R // m_b == q and m_a <= m_b
                    s0 = mult_const * (r1 - r0)
                    s1 = mh1 * (P1[r1] - P1[r0])
                    s2 = mh2 * (p2_r1 - p2_r0)
                    s3 = mh3 * (p3_r1 - p3_r0)
                    p2_r0, p3_r0 = p2_r1, p3_r1
                    sum_sr = Aq * s0 - Bq * s1 + Cq * s2
                    sum_sr_dm = Aq * (s1 - m_a * s0) - Bq * (s2 - m_a * s1) + Cq * (s3 - m_a * s2)
                    ln_a_lo = vjd._ln_lo_only(float(m_a))
                    inv_mb_lo = _NA(1.0 / float(m_b), _NINF)
                    blk_log_lo = _NA(_NA(_NA(float(sum_sr), _NINF) * ln_a_lo, _NINF) + _NA(_NA(float(sum_sr_dm), _NINF) * inv_mb_lo, _NINF), _NINF)
                    save_blk = _NA(save_blk + _NA(blk_log_lo * inv_KWm_lo, _NINF), _NINF)
                r_q_start = r_q
            return save_blk

        def record_slope_comp(m_lo: int, m_hi: int, mu: int, is_guar: bool):
            nonlocal s_lo_flt, s_hi_flt, sigma2_lo_iv, sigma2_hi_iv
            lm_hi_1 = vjd._ln_hi_only(float(m_hi))
            if use_flt_sigma2:
                s_lo_flt = _NA(s_lo_flt - _NA(float(mu) * _NA(lm_hi_1 / float(m_lo), _INF), _INF), _NINF)
                if is_guar and m_hi + dM * ((4 * m_hi) // D_lo) <= q_cap:
                    lm_lo_1 = vjd._ln_lo_only(float(m_lo))
                    s_hi_flt = _NA(s_hi_flt - _NA(float(mu) * _NA(lm_lo_1 / float(m_hi), _NINF), _NINF), _INF)
            else:
                sigma2_lo_iv = sigma2_lo_iv - cls(mu) * (cls(m_hi).ln() / cls(m_lo))
                if is_guar and m_hi + dM * ((4 * m_hi) // D_lo) <= q_cap:
                    sigma2_hi_iv = sigma2_hi_iv - cls(mu) * (cls(m_lo).ln() / cls(m_hi))
            lm_hi_mu = _NA(float(mu) * lm_hi_1, _INF)
            for m in range(m_lo, J, m_lo):
                idx_b = (m + 31) >> 5
                if idx_b <= n_blk_j:
                    diff_blk_lo[idx_b] = _NA(diff_blk_lo[idx_b] - lm_hi_mu, _NINF)

        save_k2 = 0.0
        save_k3 = 0.0
        save_k4 = 0.0
        n_comp_total = 0

        for i in range(G):
            p1_lo = guar_p_lo[i]
            p1_hi = guar_p_hi[i]
            p1_min_lo = suf_min_lo[i]
            ram1 = bool(guar_ram[i])
            if p1_hi * p1_hi > P_max and p1_min_lo * p1_min_lo > q_cap:
                break
            if p1_hi * p1_hi > P_max and p1_lo * p1_min_lo > q_cap:
                continue
            j_end_pmax = bisect.bisect_right(guar_p_hi, P_max // p1_hi, i, G)
            p2_hi_max_k3 = int((P_max // p1_hi) ** 0.5) + 1
            p2_lo_min_conv = max((high_cut_s // p1_lo) + 1, int((q_cap // p1_lo) ** 0.5) + 2)
            j_conv_start = max(
                i + 1,
                (ram_idx + 1) if ram_idx >= i else (i + 1),
                bisect.bisect_right(guar_p_hi, p2_hi_max_k3, i + 1, j_end_pmax),
                bisect.bisect_left(suf_min_lo, p2_lo_min_conv, i + 1, j_end_pmax),
            )
            for j in range(i, min(j_conv_start, G)):
                p2_hi = guar_p_hi[j]
                m2_hi = p1_hi * p2_hi
                if m2_hi > P_max and p1_lo * suf_min_lo[j] > q_cap:
                    break
                p2_lo = guar_p_lo[j]
                m2_lo = p1_lo * p2_lo
                if m2_hi > P_max and m2_lo > q_cap:
                    continue
                ram2 = bool(guar_ram[j])
                if i == j and ram1:
                    continue
                mult2 = 1 if (i == j or ram1 or ram2) else 2
                if m2_lo <= q_cap:
                    record_slope_comp(m2_lo, m2_hi, mult2, True)
                if m2_hi <= P_max:
                    n_comp_total += 1
                    in_sl2 = (m2_hi + dM * ((4 * m2_hi) // D_lo) <= q_cap)
                    lb_val = loss_lb_flt(m2_lo, m2_hi, in_sl2)
                    save_k2 = _NA(save_k2 + _NA(float(mult2) * lb_val, _NINF), _NINF)

                if m2_hi * p2_hi <= P_max or m2_lo * suf_min_lo[j] <= q_cap:
                    k_end = bisect.bisect_right(guar_p_hi, P_max // m2_hi, j, G)
                    min_p3_lo_for_high = (high_cut_s // m2_lo) + 1
                    k_conv_start = max(
                        j + 1,
                        (ram_idx + 1) if ram_idx >= j else (j + 1),
                        bisect.bisect_left(suf_min_lo, min_p3_lo_for_high, j + 1, k_end),
                    )
                    for k in range(j, min(k_conv_start, k_end)):
                        p3_hi = guar_p_hi[k]
                        m3_hi = m2_hi * p3_hi
                        if m3_hi > P_max and m2_lo * suf_min_lo[k] > q_cap:
                            break
                        p3_lo = guar_p_lo[k]
                        m3_lo = m2_lo * p3_lo
                        if m3_hi > P_max and m3_lo > q_cap:
                            continue
                        ram3 = bool(guar_ram[k])
                        if (j == k and ram2) or (i == k and ram1):
                            continue
                        distinct_split = len({idx for idx, r_flag in [(i, ram1), (j, ram2), (k, ram3)] if not r_flag})
                        mult3 = 1 << max(0, distinct_split - 1)
                        if m3_lo <= q_cap:
                            record_slope_comp(m3_lo, m3_hi, mult3, True)
                        if m3_hi <= P_max:
                            n_comp_total += 1
                            in_sl3 = (m3_hi + dM * ((4 * m3_hi) // D_lo) <= q_cap)
                            lb_val = loss_lb_flt(m3_lo, m3_hi, in_sl3)
                            save_k3 = _NA(save_k3 + _NA(float(mult3) * lb_val, _NINF), _NINF)
                    if k_conv_start < k_end:
                        distinct_split_12 = (0 if ram1 else 1) + (0 if (ram2 or j == i) else 1)
                        mult3_tail = 1 << distinct_split_12
                        save_k3 = _NA(save_k3 + sum_tail_blocks_flt(k_conv_start, k_end, m2_hi, mult3_tail), _NINF)
                        n_comp_total += (k_end - k_conv_start)
                    k_sl_start = max(j, k_end)
                    if k_sl_start < G and m2_lo * suf_min_lo[k_sl_start] <= q_cap:
                        for k in range(k_sl_start, G):
                            if m2_lo * suf_min_lo[k] > q_cap:
                                break
                            p3_lo = guar_p_lo[k]
                            m3_lo = m2_lo * p3_lo
                            if m3_lo > q_cap:
                                continue
                            ram3 = bool(guar_ram[k])
                            if (j == k and ram2) or (i == k and ram1):
                                continue
                            m3_hi = m2_hi * guar_p_hi[k]
                            distinct_split = len({idx for idx, r_flag in [(i, ram1), (j, ram2), (k, ram3)] if not r_flag})
                            mult3 = 1 << max(0, distinct_split - 1)
                            record_slope_comp(m3_lo, m3_hi, mult3, True)

                    if use_k4 and m2_hi * p2_hi * p2_hi <= P_max:
                        for k in range(j, k_end):
                            p3_lo = guar_p_lo[k]
                            p3_hi = guar_p_hi[k]
                            m3_lo, m3_hi = m2_lo * p3_lo, m2_hi * p3_hi
                            if m3_hi * p3_hi > P_max:
                                break
                            ram3 = bool(guar_ram[k])
                            if (j == k and ram2) or (i == k and ram1):
                                continue
                            r4_end = bisect.bisect_right(guar_p_hi, P_max // m3_hi, k, G)
                            if r4_end <= k:
                                break
                            min_p4_lo_for_high = (max(S, q_cols_c) // m3_lo) + 1
                            r4_conv_start = max(
                                k + 1,
                                (ram_idx + 1) if ram_idx >= k else (k + 1),
                                bisect.bisect_left(suf_min_lo, min_p4_lo_for_high, k + 1, r4_end),
                            )
                            for r4 in range(k, min(r4_conv_start, r4_end)):
                                ram4 = bool(guar_ram[r4])
                                if (r4 == k and ram3) or (r4 == j and ram2) or (r4 == i and ram1):
                                    continue
                                m4_lo, m4_hi = m3_lo * guar_p_lo[r4], m3_hi * guar_p_hi[r4]
                                d_sp4 = len({idx for idx, r_f in [(i, ram1), (j, ram2), (k, ram3), (r4, ram4)] if not r_f})
                                mult4 = 1 << max(0, d_sp4 - 1)
                                n_comp_total += 1
                                lb_val = loss_lb_flt(m4_lo, m4_hi, False)
                                save_k4 = _NA(save_k4 + _NA(float(mult4) * lb_val, _NINF), _NINF)
                            if r4_conv_start < r4_end:
                                d_pref3 = len({idx for idx, r_f in [(i, ram1), (j, ram2), (k, ram3)] if not r_f})
                                mult4_tail = 1 << d_pref3
                                save_k4 = _NA(save_k4 + sum_tail_blocks_flt(r4_conv_start, r4_end, m3_hi, mult4_tail), _NINF)
                                n_comp_total += (r4_end - r4_conv_start)

            if j_conv_start < j_end_pmax:
                mult2_tail = 1 if ram1 else 2
                save_k2 = _NA(save_k2 + sum_tail_blocks_flt(j_conv_start, j_end_pmax, p1_hi, mult2_tail), _NINF)
                n_comp_total += (j_end_pmax - j_conv_start)
            j_sl_start = max(i, j_conv_start)
            if j_sl_start < G and p1_lo * suf_min_lo[j_sl_start] <= q_cap:
                for j in range(j_sl_start, G):
                    if p1_lo * suf_min_lo[j] > q_cap:
                        break
                    p2_lo = guar_p_lo[j]
                    m2_lo = p1_lo * p2_lo
                    if m2_lo > q_cap:
                        continue
                    ram2 = bool(guar_ram[j])
                    if i == j and ram1:
                        continue
                    m2_hi = p1_hi * guar_p_hi[j]
                    mult2 = 1 if (i == j or ram1 or ram2) else 2
                    record_slope_comp(m2_lo, m2_hi, mult2, True)

            if dM > 0 and extra_sf_cands and p1_lo * extra_sf_cands[0][0] <= q_cap:
                for p2_lo, p2_hi, ram2 in extra_sf_cands:
                    m2_lo = p1_lo * p2_lo
                    if m2_lo > q_cap:
                        break
                    m2_hi = p1_hi * p2_hi
                    mult2 = 1 if (ram1 or ram2) else 2
                    record_slope_comp(m2_lo, m2_hi, mult2, False)

        del P1, P2_16, P3_16, guar_p_lo, guar_p_hi, guar_ram, suf_min_lo, extra_sf_cands
        ufd_save_lo = _NA(_NA(save_k2 + save_k3, _NINF) + save_k4, _NINF)

        if use_flt_sigma2:
            sigma2_lo_iv = cls(s_lo_flt, s_lo_flt)
            sigma2_hi_iv = cls(s_hi_flt, s_hi_flt)

        delta_D_lo_iv = cls(D_lo + 4).sqrt() / iv_4
        delta_D_hi_iv = cls(D_hi + 4).sqrt() / iv_4
        base_rad_lo_iv = ((cls(n) * cls(D_lo).sqrt()) / (iv_2 * pi_iv)).sqrt()
        base_rad_hi_iv = ((cls(n) * cls(D_hi).sqrt()) / (iv_2 * pi_iv)).sqrt()
        rho_n_lo_iv = base_rad_lo_iv + delta_D_lo_iv
        rho_n_hi_iv = base_rad_hi_iv + delta_D_hi_iv
        theta_iv = cls(M_tri) / cls(n * J)
        actual_eps_J_iv = iv_J / iv_R

        slope_j_lo_iv = (iv_R / rho_n_hi_iv).ln() - sigma2_hi_iv
        slope_j_hi_iv = (iv_R / rho_n_lo_iv).ln() - sigma2_lo_iv

        # Zero-tuple-allocation 2048-bucket outward-rounded histogram for top q_cols_h of H_blk
        sig_hi_flt = s_lo_flt if use_flt_sigma2 else (sigma2_lo_iv.hi if cls is vjd.FInterval else _NA(float(sigma2_lo_iv.hi), _INF))
        cur_fl = 0.0
        h_min = float("inf")
        h_max = float("-inf")
        pp_step32 = vjd.PP_FL_STEP32
        for b_i in range(n_blk_j):
            cur_fl = _NA(cur_fl + diff_blk_lo[b_i], _NINF)
            tot_fl = _NA(pp_step32[b_i] + cur_fl, _NINF)
            j1 = min(J, (b_i << 5) + 32)
            h_val = _NA(_NA(float(j1 - 1) * sig_hi_flt, _INF) - tot_fl, _INF)
            diff_blk_lo[b_i] = h_val
            if h_val < h_min:
                h_min = h_val
            if h_val > h_max:
                h_max = h_val

        N_BINS = 2048
        span_h = max(1e-9, h_max - h_min)
        inv_span = (N_BINS - 1) / span_h
        bin_cols = [0] * N_BINS
        bin_sum = [0.0] * N_BINS
        last_cnt = J - ((n_blk_j - 1) << 5)
        for b_i in range(n_blk_j):
            hv = diff_blk_lo[b_i]
            cnt_b = 32 if b_i + 1 < n_blk_j else last_cnt
            bi = int((hv - h_min) * inv_span)
            if bi < 0:
                bi = 0
            elif bi >= N_BINS:
                bi = N_BINS - 1
            bin_cols[bi] += cnt_b
            bin_sum[bi] = _NA(bin_sum[bi] + _NA(float(cnt_b) * hv, _INF), _INF)

        q_cols_h = M_tri // n
        r_cols_h = M_tri % n
        sum_top_H = 0.0
        rem_cols = q_cols_h
        cut_bi = 0
        for bi in range(N_BINS - 1, -1, -1):
            if rem_cols > bin_cols[bi]:
                sum_top_H = _NA(sum_top_H + bin_sum[bi], _INF)
                rem_cols -= bin_cols[bi]
            else:
                cut_bi = bi
                break

        straddle_items = []
        max_below = float("-inf")
        for b_i in range(n_blk_j):
            hv = diff_blk_lo[b_i]
            bi = int((hv - h_min) * inv_span)
            if bi < 0:
                bi = 0
            elif bi >= N_BINS:
                bi = N_BINS - 1
            if bi == cut_bi:
                cnt_b = 32 if b_i + 1 < n_blk_j else last_cnt
                straddle_items.append((hv, cnt_b))
            elif bi < cut_bi and hv > max_below:
                max_below = hv
        del diff_blk_lo

        straddle_items.sort(reverse=True)
        next_h_val = max_below
        for hv, cnt_b in straddle_items:
            if rem_cols >= cnt_b:
                sum_top_H = _NA(sum_top_H + _NA(float(cnt_b) * hv, _INF), _INF)
                rem_cols -= cnt_b
            elif rem_cols > 0:
                sum_top_H = _NA(sum_top_H + _NA(float(rem_cols) * hv, _INF), _INF)
                rem_cols = 0
                next_h_val = hv
                break
            else:
                next_h_val = hv
                break
        tot_H_ub = _NA(_NA(float(n) * sum_top_H, _INF) + _NA(float(r_cols_h) * next_h_val, _INF), _INF)

        for y, y2, blks in high_by_y2:
            base = M_lo * y2
            limit_x = P_max - base
            if limit_x < blks[0][1]:
                continue
            y_is_odd = (y & 1) == 1
            for b_x0, b_xf, b_xl, b_cnt, b_d1, b_d2, b_d3 in blks:
                if b_xf > limit_x:
                    break
                p_a = b_xf + base
                q = R // p_a
                max_p_q = (R // q) if q > 0 else P_max
                if b_xl <= limit_x and b_xl + base <= max_p_q:
                    cnt = b_cnt
                    d1, d2, d3 = b_d1, b_d2, b_d3
                    s1 = d1 + cnt * base
                    s2 = d2 + 2 * base * d1 + cnt * base * base
                    s3 = d3 + 3 * base * d2 + 3 * base * base * d1 + cnt * (base ** 3)
                    Aq = q * RRK
                    Bq = ((q * (q + 1)) >> 1) * RK2
                    Cq = (q * (q + 1) * (2 * q + 1)) // 6
                    sum_sr = Aq * cnt - Bq * s1 + Cq * s2
                    sum_sr_dp = Aq * (s1 - cnt * p_a) - Bq * (s2 - p_a * s1) + Cq * (s3 - p_a * s2)
                    ln_a_hi = vjd._ln_hi_only(float(p_a))
                    inv_pa_hi = _NA(1.0 / float(p_a), _INF)
                    blk_log = _NA(_NA(_NA(float(sum_sr), _INF) * ln_a_hi, _INF) + _NA(_NA(float(sum_sr_dp), _INF) * inv_pa_hi, _INF), _INF)
                    split_loss_hi = _NA(split_loss_hi + _NA(blk_log * inv_KWm_hi, _INF), _INF)
                else:
                    sub_xs = []
                    x_cur = b_x0
                    found_c = 0
                    while found_c < b_cnt:
                        xv = x_cur * x_cur + x_cur * y
                        if math.gcd(abs(x_cur), y) == 1 and (y_is_odd or (x_cur & 1) == 1):
                            found_c += 1
                            if xv <= limit_x:
                                sub_xs.append(xv)
                            else:
                                break
                        x_cur += 1
                    n_sub = len(sub_xs)
                    i0 = 0
                    while i0 < n_sub:
                        pa_sub = sub_xs[i0] + base
                        q_sub = R // pa_sub
                        max_pq_sub = (R // q_sub) if q_sub > 0 else P_max
                        i1 = bisect.bisect_right(sub_xs, max_pq_sub - base, i0, n_sub)
                        cnt = i1 - i0
                        d1 = d2 = d3 = 0
                        for idx_s in range(i0, i1):
                            xv = sub_xs[idx_s]
                            d1 += xv
                            xv2 = xv * xv
                            d2 += xv2
                            d3 += xv2 * xv
                        s1 = d1 + cnt * base
                        s2 = d2 + 2 * base * d1 + cnt * base * base
                        s3 = d3 + 3 * base * d2 + 3 * base * base * d1 + cnt * (base ** 3)
                        Aq = q_sub * RRK
                        Bq = ((q_sub * (q_sub + 1)) >> 1) * RK2
                        Cq = (q_sub * (q_sub + 1) * (2 * q_sub + 1)) // 6
                        sum_sr = Aq * cnt - Bq * s1 + Cq * s2
                        sum_sr_dp = Aq * (s1 - cnt * pa_sub) - Bq * (s2 - pa_sub * s1) + Cq * (s3 - pa_sub * s2)
                        ln_a_hi = vjd._ln_hi_only(float(pa_sub))
                        inv_pa_hi = _NA(1.0 / float(pa_sub), _INF)
                        blk_log = _NA(_NA(_NA(float(sum_sr), _INF) * ln_a_hi, _INF) + _NA(_NA(float(sum_sr_dp), _INF) * inv_pa_hi, _INF), _INF)
                        split_loss_hi = _NA(split_loss_hi + _NA(blk_log * inv_KWm_hi, _INF), _INF)
                        i0 = i1

        if use_flt_sigma2:
            vjd._HYBRID_PADIC_CACHE[sieve_flt_key] = (
                s_lo_flt, s_hi_flt, tot_H_ub, split_loss_hi, ufd_save_lo, save_k2, save_k3, save_k4, G1, G, n_comp_total
            )
    const_j_iv = (cls(2) * cls(tot_H_ub, tot_H_ub)) / cls(M_tri)
    unif_j_norm_iv = (iv_2 * (iv_M_tri * iv_J * (iv_1 - theta_iv / iv_2) + (theta_iv * iv_J) / iv_2)) / W_main_iv

    if use_meixner_schur:
        eta_raw_iv = delta_D_hi_iv / base_rad_lo_iv
        eta_num = int(math.ceil(float(eta_raw_iv.hi) * 10000.0))
        eta_box_iv = cls(eta_num) / cls(10000)
        while eta_box_iv.lo < eta_raw_iv.hi:
            eta_num += 1
            eta_box_iv = cls(eta_num) / cls(10000)
        assert eta_raw_iv.hi <= eta_box_iv.lo <= eta_box_iv.hi

        L_grid_den = 1000 if dM == 0 else 50
        L_lo_num = (
            int(math.floor(float(slope_j_lo_iv.lo) * 1000.0))
            if dM == 0
            else int(math.floor(float(slope_j_lo_iv.lo) * 10.0)) * 5
        )
        L_hi_num = int(math.ceil(float(slope_j_hi_iv.hi) * L_grid_den))
        if dM > 0 and L_hi_num > 209:
            L_hi_num = ((L_hi_num + 3) // 4) * 4
        L_lo_box = cls(L_lo_num) / cls(L_grid_den)
        while L_lo_box.hi > slope_j_lo_iv.lo:
            L_lo_num -= 1
            L_lo_box = cls(L_lo_num) / cls(L_grid_den)
        L_hi_box = cls(L_hi_num) / cls(L_grid_den)
        while L_hi_box.lo < slope_j_hi_iv.hi:
            L_hi_num += 1
            L_hi_box = cls(L_hi_num) / cls(L_grid_den)
        L_box_iv = cls(L_lo_box.lo, L_hi_box.hi)
        assert L_box_iv.lo <= slope_j_lo_iv.lo and slope_j_hi_iv.hi <= L_box_iv.hi

        ms_key = ("ms_var", R, S, K, J, n, eta_num, L_lo_num, L_hi_num, L_grid_den, ms_params, cls)
        if ms_key in vjd._HYBRID_PADIC_CACHE:
            arch_var_ms_iv = vjd._HYBRID_PADIC_CACHE[ms_key]
        elif ms_params is not None and len(ms_params) == 4:
            ch_raw_iv = compute_charlier_var_ub_iv(
                cls, R, S, K, J, n, eta_box_iv, L_box_iv,
                a_num=ms_params[0], a_den=ms_params[1], beta_num=ms_params[2], beta_den=ms_params[3],
            )
            arch_var_ms_iv = cls(ch_raw_iv.hi, ch_raw_iv.hi)
            vjd._HYBRID_PADIC_CACHE[ms_key] = arch_var_ms_iv
        else:
            ms_kw = (
                {}
                if ms_params is None
                else {
                    "A_num": ms_params[0],
                    "A_den": ms_params[1],
                    "v_num": ms_params[2],
                    "v_den": ms_params[3],
                    "beta_num": ms_params[4],
                    "beta_den": ms_params[5],
                    "dual_num": ms_params[6],
                    "dual_den": ms_params[7],
                }
            )
            arch_var_ms_iv = compute_meixner_schur_var_ub_iv(
                cls, R, S, K, J, R, actual_eps_J_iv, theta_iv, eta_box_iv, L_box_iv, **ms_kw
            )
            vjd._HYBRID_PADIC_CACHE[ms_key] = arch_var_ms_iv
        F_lb_iv = unif_j_norm_iv * slope_j_hi_iv - arch_var_ms_iv
        arch_norm_iv = (
            W12_norm_iv * rho_n_hi_iv.ln()
            + arch_var_ms_iv
            + (iv_M_tri * const_j_iv) / W_main_iv
            + (iv_2 * iv_M_tri * iv_M_tri.ln()) / W_main_iv
        )
    else:
        sl_grid_int = int(math.floor(float(slope_j_lo_iv.lo) * 2000.0))
        sl_grid_flt = _NA(sl_grid_int / 2000.0, _NINF)
        sl_grid_iv = cls(vjd.Decimal(sl_grid_int) / vjd.Decimal(2000)) if cls is vjd.DInterval else cls(sl_grid_flt, sl_grid_flt)
        assert sl_grid_iv.hi <= slope_j_lo_iv.lo
        deriv_key = ("deriv", M_tri, R, S, J, n, sl_grid_int, cls)
        if deriv_key in vjd._HYBRID_PADIC_CACHE:
            deriv_r_saving_lb = vjd._HYBRID_PADIC_CACHE[deriv_key]
        else:
            deriv_r_saving_lb = vjd.compute_save_deriv_exact_bins_iv(M_tri, R, S, J, theta_iv, sl_grid_iv, cls, N_deriv=3200)
            vjd._HYBRID_PADIC_CACHE[deriv_key] = deriv_r_saving_lb
        F_w_iv, dual_gap_iv, F_lb_iv = vfjc.solve_variational_fubini_jensen_iv(
            M_steps, N_num, D_den, K, rho_n_lo_iv, base_rad_lo_iv, delta_D_lo_iv,
            rho_n_hi_iv, base_rad_hi_iv, delta_D_hi_iv, n, R, J, slope_j_lo_iv, cls=cls, b0_frac=b0_frac
        )
        arch_norm_iv = (
            W12_norm_iv * rho_n_hi_iv.ln()
            + unif_j_norm_iv * slope_j_hi_iv
            - F_lb_iv
            - deriv_r_saving_lb
            + (iv_M_tri * const_j_iv) / W_main_iv
            + (iv_2 * iv_M_tri * iv_M_tri.ln()) / W_main_iv
        )

    cache_key = (P_max, K, S, R, J, n, cls)
    if cache_key in vjd._HYBRID_PADIC_CACHE:
        padic_norm_iv = vjd._HYBRID_PADIC_CACHE[cache_key]
    else:
        padic_norm_iv = iv_0
        for p in vjd.PRIMES:
            if p >= K:
                break
            w_iv = vjd.exact_rigorous_W_biconj_iv(p, K, S, R, W_main_iv, actual_eps_J_iv, theta_iv, W2_norm_iv, cls)
            padic_norm_iv = padic_norm_iv + w_iv * cls(p).ln()
        for p in vjd.PRIMES:
            if p < K:
                continue
            p_pow = p * p
            if p_pow > S:
                break
            while p_pow <= S:
                sum_s = vjd.sum_floor_s_tri(S, p_pow)
                if sum_s > 0:
                    padic_norm_iv = padic_norm_iv + (cls(2 * K * sum_s) / W_main_iv) * cls(p).ln()
                p_pow *= (p * p)
        sr_key = ("sr_int", R, K, P_max)
        if sr_key in vjd._HYBRID_PADIC_CACHE:
            sr_int = vjd._HYBRID_PADIC_CACHE[sr_key]
        else:
            sr_int = fast_sum_Sr_Lp_ext(R, K, P_max)
            vjd._HYBRID_PADIC_CACHE[sr_key] = sr_int
        padic_norm_iv = padic_norm_iv + cls(sr_int) / (cls(1 << 53) * iv_K * W_main_iv)
        vjd._HYBRID_PADIC_CACHE[cache_key] = padic_norm_iv

    split_loss_iv = cls(split_loss_hi, split_loss_hi)
    ufd_save_iv = cls(ufd_save_lo, ufd_save_lo)
    total_padic_iv = (padic_norm_iv - split_loss_iv) + ufd_save_iv
    gap_iv = total_padic_iv - arch_norm_iv
    return gap_iv.lo > 0, float(gap_iv.lo), gap_iv, {
        "G1": G1,
        "G": G,
        "padic": float(padic_norm_iv.lo),
        "split_loss": float(split_loss_iv.hi),
        "ufd_save": float(ufd_save_iv.lo),
        "save_k2": save_k2,
        "save_k3": save_k3,
        "save_k4": save_k4,
        "sigma2": float(sigma2_hi_iv.hi),
        "F_lb": float(F_lb_iv.lo),
        "arch": float(arch_norm_iv.hi),
        "n_composites": n_comp_total,
    }


