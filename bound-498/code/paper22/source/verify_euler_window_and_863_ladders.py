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


def certify_infinite_tail_euler_window(
    D_lo=855000, K=29, M_steps=800, cls=vjd.FInterval, b0_frac=0.48, eps_J_num=64, c_R_num=400
):
    i0, i1, i2, i3, i4, pi, sq3, em = _consts(cls)
    iK, X_lo = cls(K), cls(D_lo - 3) / i4
    S = (c_R_num * (D_lo - 3)) // (400 * K)
    R = K * S
    assert c_R_num <= 400 and R < D_lo
    J = (eps_J_num * R) // 1000
    iS, iR, iJ = cls(S), cls(R), cls(J)
    cR_hi, eps_hi = cls(c_R_num) / cls(100), cls(eps_J_num) / cls(1000)
    cR_lo, eps_lo = cR_hi - iK / X_lo, eps_hi - i1 / iR

    r_My = (i4 * ((cls(102) * iK) / (cls(100) * eps_lo)).sqrt() / (i2 * pi * iS * cls(D_lo).sqrt()).sqrt()
            + (i1 + (i1 + i4 / cls(D_lo)).sqrt()) / iS)
    gam_ub = i1 + r_My + (cls(M_steps) * eps_hi) / iS
    assert float(gam_ub.hi) <= 1.02
    n = (((R * S) // J + M_steps) // M_steps) * M_steps
    D_den = 1000000
    N_num = int(float((i1 / (i2 * gam_ub)).lo) * M_steps * D_den) - 1
    th_lo, th_ub = cls(N_num) / cls(M_steps * D_den), (i1 + i1 / iS) / i2
    nu_lo, nu_hi = cR_lo / (iK * eps_hi), (gam_ub * cR_hi) / (iK * eps_lo)
    eta = (cls(D_lo + 4).sqrt() / i4) / ((nu_lo * X_lo * cls(D_lo).sqrt()) / (i2 * pi)).sqrt()
    C_lo, C_hi = (nu_lo / pi).ln() / i2, ((nu_hi * (i1 + i3 / (i4 * X_lo)).sqrt()) / pi).ln() / i2 + (i1 + eta).ln()

    sig2, cj_ub = i0, i0
    for p in vjd.PRIMES:
        pk = p * p
        if pk > 1000:
            break
        lp = cls(p).ln()
        while pk <= 1000:
            sig2 = sig2 + lp / cls(pk)
            cap = (i1 / (th_lo * cls(pk))) * (i1 + cls(pk) / iJ)
            bf = min(pk, int(float((i1 / cap).lo)))
            rem = vjd.ival_max(i0, i1 - cls(bf) * cap, cls)
            avg = (cap * cls(bf * (pk - 1) - (bf * (bf - 1)) // 2) + rem * cls(max(0, pk - 1 - bf))) / cls(pk)
            cj_ub = cj_ub + i2 * avg * lp
            pk *= p

    logX = X_lo.ln()
    sl_lo, sl_hi = logX / i4 + cR_lo.ln() - C_hi - sig2, logX / i4 + cR_hi.ln() - C_lo - sig2

    save_r, exp_ns = i0, (i0 - sl_lo).exp()
    M_tri = R * (S + 1) // 2
    inv_Mt, iNd = i1 / cls(M_tri), cls(3200)
    for k in range(3200):
        ul, ur = i1 - cls(k) / iNd, i1 - cls(k + 1) / iNd
        ul2, ur2 = ul * ul, ur * ur
        jl = vjd.ival_max(i0, (i1 - th_ub * ul2) * eps_lo, cls)
        ru = vjd.ival_min(i1, (i1 + i1 / iS) * (i1 - vjd.ival_max(i0, ur2 - inv_Mt, cls).sqrt()) + i1 / iR, cls)
        js = vjd.ival_max(i0, vjd.ival_min(jl, ru - exp_ns, cls), cls)
        rm = ru - js
        gm = i0 if js.hi <= 0 else vjd.ival_max(i0, js * sl_lo + (ru * ru.ln() - rm * rm.ln() - js), cls)
        save_r = save_r + vjd.ival_max(i0, ul2 - ur2, cls) * i3 * vjd.ival_max(i0, jl * sl_lo - gm, cls)

    Jh = J + 1
    _, _, F_lb = vfjc.solve_variational_fubini_jensen_iv(
        M_steps, N_num, D_den, K, i1, i1, i0, i1 + eta, i1, eta,
        n, R, Jh, sl_lo, cls=cls, b0_frac=b0_frac, L_blocks=320, J_quad=J - 1, tail_mode=True, theta_ub_iv=th_ub
    )
    unif_ub = (cls(3 * (S + 1)) / cls(R * S)) * cls(Jh) * (i1 - th_lo / i2) + (i3 * th_ub * cls(Jh)) / cls(R * R * S)
    W12_main = i1 + i1 / iK + cls(max(0, K - 5)) / cls(2 * K * S * S)
    arch = (W12_main * ((i3 / i4) * logX + C_hi) + unif_ub * sl_hi - F_lb - save_r
            + (cls(3 * (S + 1)) / cls(2 * R * S)) * cj_ub + (cls(3 * (S + 1)) / cls(R * S)) * cls(M_tri).ln())

    padic, sum_sK = i0, i0
    for p in vjd.PRIMES:
        if p < K:
            lp = cls(p).ln()
            sum_sK = sum_sK + lp / cls(p)
            padic = padic + vjd.exact_rigorous_W_biconj_tail_iv(p, K, S, cls(Jh) / iR, th_lo, cls) * lp
        else:
            pp = p * p
            if pp > S:
                break
            while pp <= S:
                sp2 = vjd.ival_max(i0, i1 / cls(K * pp) - cls(3) / cls(2 * R) + cls(3) / cls(2 * R * pp)
                                   - cls(pp) / (i2 * sq3 * iK * cls(S ** 3)), cls)
                padic = padic + sp2 * cls(p).ln()
                pp *= (p * p)

    logR_lo, logR_hi = logX + cR_lo.ln(), logX + cR_hi.ln()
    # Grouping all three 1/S(D) terms across sum_1p (+3/(2*S(D))), -bR_loss (-3/(2*S(D))),
    # and -W_12/W_main * log(rho_n) (-3*(K-1)/(2*K*S(D))) over their exact common denominator S(D):
    #   Delta_{1/S}(D) >= [C_1S(D_lo) + (3*(K+3)/(8*K))*log(X(D)/X_lo)] / S(D).
    # Because C_1S(D_lo) > 0 and 3*(K+3)/(8*K) > 0, Delta_{1/S}(D) > 0 for all D >= D_lo,
    # so bounding Delta_{1/S}(D) >= 0 from below by 0 leaves c1p = 1 and W12_main = 1 + 1/K + (K-5)_+/(2*K*S_lo^2).
    sum_1p_base = (logR_lo + em - i1 / (i2 * logR_lo)) - sum_sK
    C_1S = ((i3 / i2) * sum_1p_base - (i3 / i2) * (i1 + i1 / (i2 * logR_lo))
            - (cls(3 * (K - 1)) / (i2 * iK)) * ((i3 / i4) * logX + C_hi))
    assert float(C_1S.lo) > 0.0
    c1p = i1
    sum_1p = c1p * sum_1p_base
    bR_loss = (i1 + i1 / (cls(12) * sq3)) * (i1 + i1 / (i2 * logR_lo))
    I_gp = lambda a, b: (b * b - a * a) / i4 - (b * b * b - a * a * a) / (cls(18) * sq3)
    igp_loss = I_gp(i0, i1 / cls(16)) * (cls(101624) / cls(100000))
    for k in range(1, 16):
        ua, ub = cls(k) / cls(16), cls(k + 1) / cls(16)
        igp_loss = igp_loss + I_gp(ua, ub) * (i1 + i1 / (i2 * (iR * ua).ln()))

    u_min, w_um, i_eu = i1 / cR_hi, i0, i0
    for m in range(1, int(float(cR_hi.hi)) + 1):
        am = vjd.ival_max(i0, i1 - cls(m) * u_min, cls)
        am2, am15 = am * am, am * am.sqrt()
        w_um = w_um + i3 * am2 + (cls(3) / cls(S)) * am
        i_eu = i_eu + ((cls(8) / cls(5)) * (am2 * am.sqrt()) + (cls(2) / cls(S)) * am15) / cls(m).sqrt()
    eu_loss = (logR_hi / iR) * w_um + (logR_hi / iR.sqrt()) * i_eu

    gap = (padic + sum_1p - bR_loss - igp_loss - eu_loss) - arch
    slope = c1p - (i3 / i4) * (W12_main + unif_ub)
    return gap.lo > 0 and float(slope.lo) > 0.11, float(gap.lo), float(slope.lo), gap, {"euler_loss": float(eu_loss.hi), "C_1S": float(C_1S.lo)}


def certify_fixed_param_euler_window(
    D_lo, D_hi, K=29, M_steps=800, mode="rs_thm18", cls=vjd.FInterval, b0_frac=0.48, eps_J_num=62, c_R_num=400
):
    P_max, M_lo = (D_lo - 3) // 4, (D_lo + 1) // 4
    S = max(10, (c_R_num * P_max) // (100 * K))
    R = K * S
    assert R < D_lo
    J, M_tri = max(2, (eps_J_num * R) // 1000), R * (S + 1) // 2
    W_1, W_2 = (R * R * (S + 1) * (2 * S + 1)) // (6 * S) - M_tri, (R * (S * S - 1)) // 3
    dd_hi_f, n = math.sqrt(D_hi + 4.0) / 4.0, (R * S) // J + 1
    for _ in range(30):
        rn_f = math.sqrt(n * math.sqrt(D_hi) / (2.0 * math.pi)) + dd_hi_f
        My = 2 * int(2.0 * rn_f / math.sqrt(D_lo)) + 1
        assert max(J, int(2.0 * rn_f) + 1) <= R + My * K
        nr = (R * S + My * R) // J + 1
        if n >= nr:
            break
        n = nr
    n = ((n + M_steps - 1) // M_steps) * M_steps
    N_num, D_den = M_tri, (n // M_steps) * J

    i0, i1, i2, i3, i4, pi, sq3, em = _consts(cls)
    iK, iS, iR, iJ, iMt = cls(K), cls(S), cls(R), cls(J), cls(M_tri)
    Wm = cls(R * R * S) / i3
    W2_n, W12_n = cls(W_2) / Wm, cls(W_1 + W_2) / Wm
    dd_lo, dd_hi = cls(D_lo + 4).sqrt() / i4, cls(D_hi + 4).sqrt() / i4
    br_lo, br_hi = ((cls(n) * cls(D_lo).sqrt()) / (i2 * pi)).sqrt(), ((cls(n) * cls(D_hi).sqrt()) / (i2 * pi)).sqrt()
    rn_lo, rn_hi = br_lo + dd_lo, br_hi + dd_hi
    th, eps_iv = cls(M_tri) / cls(n * J), iJ / iR

    sig2 = i0
    for p in vjd.PRIMES:
        pk = p * p
        if pk > J - 1:
            break
        lp = cls(p).ln()
        while pk <= J - 1:
            sig2 = sig2 + lp / cls(pk)
            pk *= p
    sl_lo, sl_hi = (iR / rn_hi).ln() - sig2, (iR / rn_lo).ln() - sig2
    sh_f = sig2.hi if cls is vjd.FInterval else vjd._NA(float(sig2.hi), vjd._INF)
    H_ub = sorted([vjd._NA(vjd._NA(float(j) * sh_f, vjd._INF) - vjd.PP_FL[j], vjd._INF) for j in range(J)], reverse=True)
    qc, rc, s_H = M_tri // n, M_tri % n, 0.0
    for j in range(qc):
        s_H = vjd._NA(s_H + H_ub[j], vjd._INF)
    tot_H = vjd._NA(vjd._NA(float(n) * s_H, vjd._INF) + vjd._NA(float(rc) * H_ub[qc], vjd._INF), vjd._INF)
    cj_iv = (i2 * cls(tot_H, tot_H)) / iMt

    save_r = vjd.compute_save_deriv_exact_bins_iv(M_tri, R, S, J, th, sl_lo, cls, N_deriv=3200)
    _, _, F_lb = vfjc.solve_variational_fubini_jensen_iv(
        M_steps, N_num, D_den, K, rn_lo, br_lo, dd_lo, rn_hi, br_hi, dd_hi, n, R, J, sl_lo, cls=cls, b0_frac=b0_frac
    )
    unif_s = iMt * iJ * (i1 - th / i2) + (th * iJ) / i2
    U_arch = (W12_n * rn_hi.ln() + ((i2 * unif_s) / Wm) * sl_hi - F_lb - save_r + (iMt * cj_iv + i2 * iMt * iMt.ln()) / Wm)

    L_pad, sum_sK, th_Km1 = i0, i0, i0
    for p in vjd.PRIMES:
        if p < K:
            lp = cls(p).ln()
            sum_sK, th_Km1 = sum_sK + lp / cls(p), th_Km1 + lp
            L_pad = L_pad + vjd.exact_rigorous_W_biconj_iv(p, K, S, R, Wm, eps_iv, th, W2_n, cls) * lp
        else:
            if p * p > S or p > P_max:
                break
            pp, se = p * p, 0
            while pp <= S:
                se += vjd.sum_floor_s_tri(S, pp)
                pp *= (p * p)
            L_pad = L_pad + (cls(2 * K * se) / Wm) * cls(p).ln()

    eu_loss, KWm, x = i0, iK * Wm, 0
    while x * x + x + M_lo < R:
        px = x * x + x + M_lo
        eu_loss = eu_loss + (cls(vjd.S_r_exact(R, K, px)) / KWm) * cls(px).ln()
        x += 1

    if mode == "exact_primes":
        L_pad = L_pad + cls(vjd.fast_sum_Sr_Lp(R, K, R)) / (cls(1 << 53) * KWm) - eu_loss
    else:
        assert R <= 100000000
        logR = iR.ln()
        sum_1p = (i1 + cls(3 * K) / cls(2 * R)) * ((logR + em - i1 / (i2 * logR)) - sum_sK)
        gR_loss = (cls(5) / i4 + cls(3 * K) / cls(2 * R) + i1 / (cls(36) * sq3) - cls(K * K) / cls(4 * R * R)
                   + cls(K ** 3) / (cls(18) * sq3 * cls(R ** 3)) - (cls(3 * R + 2 * K) / cls(2 * R * R)) * th_Km1)
        L_pad = L_pad + sum_1p - gR_loss - eu_loss

    gap = L_pad - U_arch
    return gap.lo > 0, float(gap.lo), gap, {"euler_loss": float(eu_loss.hi)}


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
    if not hasattr(vjd, "PP_FL_STEP32") or len(vjd.PP_FL_STEP32) < n_blk:
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
    low_y = array.array("I")
    low_x2_xy = array.array("i")
    high_by_y2 = []
    y = 1
    while (4 * M_min - 1) * y * y <= 4 * P_max:
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
                low_y.append(y)
                low_x2_xy.append(x2_xy)
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
        if b_cnt > 0:
            blks.append((b_x0, b_xf, b_xl, b_cnt, b_d1, b_d2, b_d3))
        if blks:
            high_by_y2.append((y, y2, blks))
        y += 1
    _RAW_CAND_CACHE[key] = ((low_x, low_y, low_x2_xy), high_by_y2)
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
    upper bound (mira_cairn [16, 21]; node-block Fischer decomposition [20]).
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
    use_wronskian: bool = False,
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
    if use_wronskian:
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
    (low_x, low_y, low_x2_xy), high_by_y2 = get_raw_cands_cached(M_cache_key, P_max, low_cut_cache)

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
        n_low_raw = len(low_x)
        for idx_r in range(n_low_raw):
            y = low_y[idx_r]
            x2_xy = low_x2_xy[idx_r]
            y2 = y * y
            p_lo_raw = x2_xy + M_lo * y2
            if p_lo_raw <= tier1_bound:
                x = low_x[idx_r]
                is_ram = (y == 2 and x == -1)
                p_hi_raw = x2_xy + M_hi * y2
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
        raw_g_hi = array.array("I")
        raw_g_ram = bytearray()
        extra_sf_cands = []
        split_loss_hi = 0.0

        m_lo_sq = M_lo * M_lo
        for idx_r in range(n_low_raw):
            x = low_x[idx_r]
            y = low_y[idx_r]
            x2_xy = low_x2_xy[idx_r]
            y2 = y * y
            is_ram = (y == 2 and x == -1)
            p_lo_raw = x2_xy + M_lo * y2
            p_hi_raw = x2_xy + M_hi * y2
            if p_lo_raw <= max_factor:
                u = 2 * x + y
                if p_lo_raw < m_lo_sq or not comp2_grid[y * stride + u]:
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
        order = sorted(range(G), key=lambda idx: (raw_g_hi[idx], raw_g_lo[idx], raw_g_ram[idx]))
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

        P1 = [0] * (G + 1)
        P2 = [0] * (G + 1)
        P3 = [0] * (G + 1)
        a1 = a2 = a3 = 0
        for idx_g, ph in enumerate(guar_p_hi):
            a1 += ph
            ph2 = ph * ph
            a2 += ph2
            a3 += ph2 * ph
            P1[idx_g + 1] = a1
            P2[idx_g + 1] = a2
            P3[idx_g + 1] = a3

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
                for r0 in range(r_q_start, r_q, 16):
                    r1 = r0 + 16
                    if r1 > r_q:
                        r1 = r_q
                    m_a = m_pref_hi * guar_p_hi[r0]
                    m_b = m_pref_hi * guar_p_hi[r1 - 1]
                    assert R // m_b == q and m_a <= m_b
                    s0 = mult_const * (r1 - r0)
                    s1 = mh1 * (P1[r1] - P1[r0])
                    s2 = mh2 * (P2[r1] - P2[r0])
                    s3 = mh3 * (P3[r1] - P3[r0])
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

        del P1, P2, P3, guar_p_lo, guar_p_hi, guar_ram, suf_min_lo, extra_sf_cands
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

        L_lo_num = int(math.floor(float(slope_j_lo_iv.lo) * 10.0)) * 5
        L_hi_num = int(math.ceil(float(slope_j_hi_iv.hi) * 50.0))
        if L_hi_num > 209:
            L_hi_num = ((L_hi_num + 3) // 4) * 4
        L_lo_box = cls(L_lo_num) / cls(50)
        while L_lo_box.hi > slope_j_lo_iv.lo:
            L_lo_num -= 1
            L_lo_box = cls(L_lo_num) / cls(50)
        L_hi_box = cls(L_hi_num) / cls(50)
        while L_hi_box.lo < slope_j_hi_iv.hi:
            L_hi_num += 1
            L_hi_box = cls(L_hi_num) / cls(50)
        L_box_iv = cls(L_lo_box.lo, L_hi_box.hi)
        assert L_box_iv.lo <= slope_j_lo_iv.lo and slope_j_hi_iv.hi <= L_box_iv.hi

        ms_key = ("ms_var", R, S, K, J, n, eta_num, L_lo_num, L_hi_num, ms_params, cls)
        if ms_key in vjd._HYBRID_PADIC_CACHE:
            arch_var_ms_iv = vjd._HYBRID_PADIC_CACHE[ms_key]
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


def verify_tail_block_and_ordering_invariants():
    import decimal
    R_test, K_test, m_pref_test, mult_test = 907199992, 19, 34496, 4
    RRK_t = R_test * (R_test + K_test)
    RK2_t = 2 * R_test + K_test
    # 1. Raw pairs on [699, 703] where sorting by p_lo left p_hi unordered across quotient q=2 / q=1 boundary,
    #    plus synthetic multi-quotient pairs spanning q in {1, 2, ..., 12} with large dM*y^2 inversions
    raw_pairs = [
        (13088, 13097),
        (13057, 13058),
        (13127, 13136),
        (13159, 13168),
        (13137, 13138),
    ]
    for q_t in range(1, 13):
        p_knot = (R_test // q_t) // m_pref_test
        for delta in (-19, -7, -2, -1, 0, 1, 2, 8, 21):
            p_lo_v = max(175, p_knot + delta)
            y_sim = 1 + ((abs(delta) * 7 + q_t) % 60)
            p_hi_v = p_lo_v + y_sim * y_sim
            raw_pairs.append((p_lo_v, p_hi_v))

    sorted_pairs = sorted(raw_pairs, key=lambda x: (x[1], x[0]))
    g_lo = [x[0] for x in sorted_pairs]
    g_hi = [x[1] for x in sorted_pairs]
    suf_lo = [0] * len(g_lo)
    cur_m = g_lo[-1]
    for idx in range(len(g_lo) - 1, -1, -1):
        cur_m = min(cur_m, g_lo[idx])
        suf_lo[idx] = cur_m
    assert all(g_hi[idx] <= g_hi[idx + 1] for idx in range(len(g_hi) - 1))
    assert all(suf_lo[idx] <= suf_lo[idx + 1] for idx in range(len(suf_lo) - 1))
    for idx in range(len(g_lo)):
        assert suf_lo[idx] == min(g_lo[idx:]) and suf_lo[idx] <= g_lo[idx] <= g_hi[idx]

    # Also verify specifically on the referee's 5-element subset
    ref_sorted = sorted([(13088, 13097), (13057, 13058), (13127, 13136), (13159, 13168), (13137, 13138)], key=lambda x: (x[1], x[0]))
    assert [x[1] for x in ref_sorted] == [13058, 13097, 13136, 13138, 13168]

    ctx = decimal.Context(prec=60, rounding=decimal.ROUND_FLOOR)
    for seq_hi in [[x[1] for x in ref_sorted], g_hi]:
        P1, P2, P3 = [0], [0], [0]
        for ph in seq_hi:
            P1.append(P1[-1] + ph)
            P2.append(P2[-1] + ph * ph)
            P3.append(P3[-1] + ph * ph * ph)
        r0, r_end = 0, len(seq_hi)
        tot_blk_lo = 0.0
        tot_exact_dec = decimal.Decimal(0)
        n_blks = 0
        while r0 < r_end:
            pa = seq_hi[r0]
            m_a = m_pref_test * pa
            q = R_test // m_a
            if q <= 0:
                break
            n_blks += 1
            max_p_q = (R_test // q) // m_pref_test
            r_q = bisect.bisect_right(seq_hi, max_p_q, r0, r_end)
            r1 = min(r_q, r0 + 16)
            pb = seq_hi[r1 - 1]
            m_b = m_pref_test * pb
            assert R_test // m_b == q and m_a <= m_b
            c0 = r1 - r0
            d1 = P1[r1] - P1[r0]
            d2 = P2[r1] - P2[r0]
            d3 = P3[r1] - P3[r0]
            s0 = mult_test * c0
            mh1 = mult_test * m_pref_test
            s1 = mh1 * d1
            mh2 = mh1 * m_pref_test
            s2 = mh2 * d2
            s3 = (mh2 * m_pref_test) * d3
            Aq = q * RRK_t
            Bq = ((q * (q + 1)) >> 1) * RK2_t
            Cq = (q * (q + 1) * (2 * q + 1)) // 6
            sum_sr = Aq * s0 - Bq * s1 + Cq * s2
            sum_sr_dm = Aq * (s1 - m_a * s0) - Bq * (s2 - m_a * s1) + Cq * (s3 - m_a * s2)
            ln_a_lo = vjd._ln_lo_only(float(m_a))
            inv_mb_lo = _NA(1.0 / float(m_b), _NINF)
            blk_log_lo = _NA(_NA(_NA(float(sum_sr), _NINF) * ln_a_lo, _NINF) + _NA(_NA(float(sum_sr_dm), _NINF) * inv_mb_lo, _NINF), _NINF)
            blk_dec = decimal.Decimal(0)
            for idx in range(r0, r1):
                mr = m_pref_test * seq_hi[idx]
                assert R_test // mr == q and m_a <= mr <= m_b
                sr_exact = vjd.S_r_exact(R_test, K_test, mr)
                blk_dec = ctx.add(blk_dec, ctx.multiply(decimal.Decimal(mult_test * sr_exact), ctx.ln(decimal.Decimal(mr))))
            assert decimal.Decimal(blk_log_lo) <= blk_dec, f"Block {n_blks} LB {blk_log_lo} > {blk_dec}"
            tot_blk_lo = _NA(tot_blk_lo + blk_log_lo, _NINF)
            tot_exact_dec = ctx.add(tot_exact_dec, blk_dec)
            r0 = r1
        assert decimal.Decimal(tot_blk_lo) < tot_exact_dec
        if len(seq_hi) == 5:
            assert n_blks == 2
            ref_blk_lo, ref_dec = tot_blk_lo, tot_exact_dec
    # 2. Verify (dM+1)-point Discrete Discriminant Comb exact coverage, pointwise factorwise norm monotonicity,
    #    and exhaustive candidate audit across 100% of candidates on [831, 835]
    D_lo_c, D_hi_c = 691, 695
    dM_c = (D_hi_c - D_lo_c) // 4
    assert dM_c == 1
    for x1, y1 in [(0, 1), (-1, 2), (1, 3), (-4, 5)]:
        u1 = 2 * x1 + y1
        p1_lo = x1 * x1 + x1 * y1 + ((D_lo_c + 1) // 4) * y1 * y1
        p1_hi = x1 * x1 + x1 * y1 + ((D_hi_c + 1) // 4) * y1 * y1
        for x2, y2 in [(0, 1), (2, 3), (-3, 7)]:
            u2 = 2 * x2 + y2
            p2_lo = x2 * x2 + x2 * y2 + ((D_lo_c + 1) // 4) * y2 * y2
            p2_hi = x2 * x2 + x2 * y2 + ((D_hi_c + 1) // 4) * y2 * y2
            m_lo_prod = p1_lo * p2_lo
            m_hi_prod = p1_hi * p2_hi
            yp = (u1 * y2 + u2 * y1) // 2
            ym = abs(u2 * y1 - u1 * y2) // 2
            disc_up = {abs(u1 * u2 - (D_lo_c + 4 * m) * y1 * y2) // 2 for m in range(dM_c + 1)}
            disc_um = {(u1 * u2 + (D_lo_c + 4 * m) * y1 * y2) // 2 for m in range(dM_c + 1)}
            for D_m in (D_lo_c, D_hi_c):
                M_m = (D_m + 1) // 4
                p1 = x1 * x1 + x1 * y1 + M_m * y1 * y1
                p2 = x2 * x2 + x2 * y2 + M_m * y2 * y2
                up = abs(u1 * u2 - D_m * y1 * y2) // 2
                um = (u1 * u2 + D_m * y1 * y2) // 2
                assert up in disc_up and um in disc_um
                norm_p = (up * up + D_m * yp * yp) // 4
                norm_m = (um * um + D_m * ym * ym) // 4
                assert norm_p == p1 * p2 and norm_m == p1 * p2
                assert m_lo_prod <= norm_p <= m_hi_prod
                p_hi_p = norm_p + ((D_hi_c - D_m) // 4) * yp * yp
                p_hi_m = norm_m + ((D_hi_c - D_m) // 4) * ym * ym
                assert p_hi_p <= m_hi_prod + dM_c * ((4 * m_hi_prod) // D_lo_c)
                assert p_hi_m <= m_hi_prod + dM_c * ((4 * m_hi_prod) // D_lo_c)

    # Exhaustive 100% candidate audit on [831, 835] (M_lo = 208, M_hi = 209, dM = 1)
    D_lo_a, D_hi_a = 831, 835
    M_lo_a, M_hi_a = (D_lo_a + 1) // 4, (D_hi_a + 1) // 4
    dM_a = M_hi_a - M_lo_a
    for P_max_a in (8999999, 36000000):
        max_fac_a = min(P_max_a // M_lo_a, (M_lo_a ** 3) - 1)
        comp2_bound_a = max_fac_a + dM_a * ((4 * max_fac_a) // D_lo_a)
        t1_bound_a = comp2_bound_a // M_lo_a
        cands_a = []
        y_lim_a = int((4 * comp2_bound_a / D_lo_a) ** 0.5) + 2
        for y in range(1, y_lim_a + 1):
            y2 = y * y
            x = -(y // 2)
            if 2 * x + y < 0:
                x += 1
            while True:
                x2_xy = x * x + x * y
                p_lo_r = x2_xy + M_lo_a * y2
                if p_lo_r > comp2_bound_a:
                    break
                if math.gcd(abs(x), y) == 1 and ((y & 1) == 1 or (x & 1) == 1):
                    p_hi_r = x2_xy + M_hi_a * y2
                    cands_a.append((p_lo_r, p_hi_r, (y == 2 and x == -1), x, y))
                x += 1
        t1_a = sorted(c for c in cands_a if c[0] <= t1_bound_a)
        Y_max_a = int((4 * comp2_bound_a / D_lo_a) ** 0.5) + 2
        U_max_a = int((4 * comp2_bound_a) ** 0.5) + 2
        stride_a = U_max_a + 1
        grid_a = bytearray((Y_max_a + 1) * stride_a)
        exact_comp_coords = set()
        for i in range(len(t1_a)):
            p1_lo, p1_hi, ram1, x1, y1 = t1_a[i]
            if p1_lo * p1_lo > comp2_bound_a:
                break
            u1 = 2 * x1 + y1
            for j in range(i, len(t1_a)):
                p2_lo, p2_hi, ram2, x2, y2 = t1_a[j]
                if p1_lo * p2_lo > comp2_bound_a:
                    break
                if i == j and ram1:
                    continue
                u2 = 2 * x2 + y2
                m_lo_ij, m_hi_ij = p1_lo * p2_lo, p1_hi * p2_hi
                yp = (u1 * y2 + u2 * y1) // 2
                for m_step in range(dM_a + 1):
                    dm = D_lo_a + 4 * m_step
                    up_m = abs(u1 * u2 - dm * y1 * y2) // 2
                    norm_dm = (up_m * up_m + dm * yp * yp) // 4
                    assert m_lo_ij <= norm_dm <= m_hi_ij
                    assert norm_dm + (D_hi_a - dm) // 4 * yp * yp <= m_hi_ij + dM_a * ((4 * m_hi_ij) // D_lo_a)
                    if yp <= Y_max_a and up_m <= U_max_a:
                        grid_a[yp * stride_a + up_m] = 1
                        exact_comp_coords.add((yp, up_m))
                if i != j and not (ram1 or ram2):
                    ym = abs(u2 * y1 - u1 * y2) // 2
                    for m_step in range(dM_a + 1):
                        dm = D_lo_a + 4 * m_step
                        um_m = (u1 * u2 + dm * y1 * y2) // 2
                        norm_dm = (um_m * um_m + dm * ym * ym) // 4
                        assert m_lo_ij <= norm_dm <= m_hi_ij
                        assert norm_dm + (D_hi_a - dm) // 4 * ym * ym <= m_hi_ij + dM_a * ((4 * m_hi_ij) // D_lo_a)
                        if ym <= Y_max_a and um_m <= U_max_a:
                            grid_a[ym * stride_a + um_m] = 1
                            exact_comp_coords.add((ym, um_m))
        n_audited = 0
        for p_lo_r, p_hi_r, is_ram, x, y in cands_a:
            if p_lo_r <= max_fac_a:
                u = 2 * x + y
                in_grid = bool(grid_a[y * stride_a + u])
                in_exact = (y, u) in exact_comp_coords
                assert in_grid == in_exact
                if p_lo_r < M_lo_a * M_lo_a:
                    assert not in_grid
                n_audited += 1
        assert n_audited in (1445, 5706)
    print(f"  [Ordering & Quotient-Split Audit] Verified referee 5-norm block (2 quotient blocks q=2, q=1: blk_lo={int(ref_blk_lo)} < exact_dec={ref_dec:.2f}), {n_blks} multi-quotient blocks, and 100% candidate audit (1445 at 9M, {n_audited} at 36M) on [831, 835].")


def verify_1_over_S_and_column_fractional_part():
    from fractions import Fraction
    for K, S, n in [(19, 100, 12000), (29, 29482, 1827200), (31, 90788, 1566400), (53, 1207547, 24152800)]:
        R = K * S
        M_tri = R * (S + 1) // 2
        W_1 = (R * R * (S + 1) * (2 * S + 1)) // (6 * S) - M_tri
        W_2 = (R * (S * S - 1)) // 3
        W_main = Fraction(R * R * S, 3)
        exact_ratio = Fraction(W_1 + W_2, 1) / W_main
        formula_ratio = (
            Fraction(1, 1)
            + Fraction(1, K)
            + Fraction(3 * (K - 1), 2 * K * S)
            + Fraction(K - 5, 2 * K * S * S)
        )
        assert exact_ratio == formula_ratio
        for q in [2, 3, 5, 7, 13, 29]:
            x = Fraction(M_tri, n * q)
            b = int(x)
            frac_x = x - b
            lhs_lin = Fraction(b * (b - 1), 2) + (x - b) * b
            rhs_quad = Fraction(x * (x - 1), 2) + Fraction(frac_x * (1 - frac_x), 2)
            assert lhs_lin == rhs_quad and rhs_quad >= Fraction(x * (x - 1), 2)
            tot_floors = M_tri // q
            b_col, r_col = divmod(tot_floors, n)
            assert b_col == b
            sum_binom = (n - r_col) * (b_col * (b_col - 1) // 2) + r_col * ((b_col + 1) * b_col // 2)
            if M_tri % q == 0:
                assert Fraction(sum_binom, n) == rhs_quad
            assert x == Fraction(R * (S + 1), 2 * n * q) > Fraction(R * S, 2 * n * q)
    for K, S, J in [(5, 3, 4), (5, 4, 6), (43, 120, 645)]:
        assert J >= S and 2 * (J + 1) <= (K + 1) * S
        A_closed = ((K - 1) * S * (S + 1)) // (2 * (J - S + 1))
        A_max = max(
            S - T + (m * (K * T - 1) - (K + 1) * m * (m - 1) // 2) // (J - m + 1)
            for T in range(1, S + 1)
            for m in range(1, T + 1)
        )
        assert A_max == A_closed
    print("  [1/S, Column Fractional-Part & Wronskian A(K,S,J) Audit] Verified exact W_12/W_main identity, {x}(1-{x})/2 >= 0, and Wronskian A(K,S,J) maximum.")


def main():
    t0 = time.time()
    print("=== 0. Prefix-Sum Convolution Ordering, Quotient-Boundary & 1/S Fractional-Part Audit ===")
    verify_tail_block_and_ordering_invariants()
    verify_1_over_S_and_column_fractional_part()
    print("=== 1. Analytical Infinite Tail [855,000, infty) (RS Thms 4, 6, 9 ONLY + y=1 Euler Window) ===")
    ok_f, gap_f, slope_f, _, det_f = certify_infinite_tail_euler_window(855000, cls=vjd.FInterval)
    ok_d, _, slope_d, gap_div, det_d = certify_infinite_tail_euler_window(855000, cls=vjd.DInterval)
    print(f"  [FInterval] D_tail = 855,000: ok={ok_f}, gap={gap_f:+.9f}, slope={slope_f:.6f}, C_1S={det_f['C_1S']:+.6f}, euler_loss={det_f['euler_loss']:.6f}")
    print(f"  [DInterval] D_tail = 855,000: ok={ok_d}, gap=[{gap_div.lo}, {gap_div.hi}], slope={slope_d:.6f}, C_1S={det_d['C_1S']:+.6f}")
    assert ok_f and ok_d and det_d["C_1S"] > 0.48

    for label, mode_str, start_d, end_d in [
        ("2. Contiguous RS Theorem 18 Ladder [641,003, 855,000]", "rs_thm18", 641003, 855000),
        ("3. Contiguous Exact-Prime 1D Euler-Window Ladder [503,003, 641,003]", "exact_primes", 503003, 641003),
    ]:
        print(f"\n=== {label} ===")
        cur, ivals = start_d, []
        while cur < end_d:
            step = min(1000 if cur < start_d + 4000 else (2500 if cur < start_d + 22000 else (5000 if cur < start_d + 58000 else 10000)), end_d - cur)
            ok, gap_val, _, info = certify_fixed_param_euler_window(cur, cur + step, mode=mode_str, cls=vjd.FInterval)
            assert ok, f"Failed {mode_str} at [{cur}, {cur+step}]"
            ivals.append((cur, cur + step, gap_val, info["euler_loss"]))
            cur += step
        ok_bd, _, gap_bdiv, _ = certify_fixed_param_euler_window(ivals[0][0], ivals[0][1], mode=mode_str, cls=vjd.DInterval)
        print(f"  Certified [{start_d:,}, {end_d:,}] in {len(ivals)} intervals (min gap = {min(x[2] for x in ivals):+.6f})")
        print(f"    Bottom [DInterval] [{ivals[0][0]:,}, {ivals[0][1]:,}]: ok={ok_bd}, gap=[{gap_bdiv.lo}, {gap_bdiv.hi}]")
        assert ok_bd

    print("\n=== 4. Fubini-Jensen Hybrid 2D Norm-Form Certification on [863, 879] ===")
    def patched_solve(M_steps, N_num, D_den, K, rho_lo, brad_lo, dd_lo, rho_hi, brad_hi, dd_hi, n, R, J, ramps_iv, cls, b0_frac=0.60):
        sl_lo, M_tri, S = ramps_iv, N_num, R // K
        th = cls(M_tri) / cls(n * J)
        i0, i1, i2, i3 = cls(0), cls(1), cls(2), cls(3)
        iM, iR, iS, iJ, iMt = cls(M_steps), cls(R), cls(S), cls(J), cls(M_tri)
        d800, exp_ns = i0, (i0 - sl_lo).exp()
        for k in range(M_steps):
            ul, ur = i1 - cls(k) / iM, i1 - cls(k + 1) / iM
            jl = vjd.ival_max(i0, (i1 - th * (ul * ul)) * iJ - i1, cls) / iR
            ru = vjd.ival_min(i1, (i1 + i1 / iS) * (cls(k + 1) / iM) + i1 / iR, cls)
            js = vjd.ival_max(i0, vjd.ival_min(jl, ru - exp_ns, cls), cls)
            rm = ru - js
            gm = i0 if js.hi <= 0 else vjd.ival_max(i0, js * sl_lo + (ru * ru.ln() - rm * rm.ln() - js), cls)
            d800 = d800 + vjd.ival_max(i0, (i2 * ur) / iM - i1 / iMt, cls) * i3 * vjd.ival_max(i0, jl * sl_lo - gm, cls)
        d3200 = vjd.compute_save_deriv_exact_bins_iv(M_tri, R, S, J, th, sl_lo, cls, N_deriv=3200)
        ex = vjd.ival_max(i0, d3200 - cls(d800.hi, d800.hi), cls)
        Fw, dgap, Flb = vfjc.solve_variational_fubini_jensen_iv(
            M_steps, N_num, D_den, K, rho_lo, brad_lo, dd_lo, rho_hi, brad_hi, dd_hi, n, R, J, sl_lo, cls=cls, b0_frac=0.48
        )
        return Fw + ex, dgap, Flb + cls(ex.lo, ex.lo)

    vjd.build_staircase_ramps_iv = lambda J, R, n, M_tri, sl_lo, cls=vjd.FInterval, **kw: sl_lo
    vjd.solve_variational_hockey_staircase_iv = patched_solve

    for d in [863, 867, 871, 875]:
        ok_hf, gap_hf, _, det_hf = vjd.certify_hybrid_interval(d, d + 4, P_max=8999999, K=23, c_R_num=14, eps_J_num=56, Q_guar=750000, cls=vjd.FInterval)
        print(f"  [FInterval] [{d}, {d+4}]: ok={ok_hf}, gap={gap_hf:+.6f}, F_lb={det_hf['F_lb']:.6f}, dgap={det_hf['duality_gap']:.2e}")
        assert ok_hf
    ok_hd, _, gap_hdiv, _ = vjd.certify_hybrid_interval(863, 867, P_max=8999999, K=23, c_R_num=14, eps_J_num=56, Q_guar=750000, cls=vjd.DInterval)
    print(f"  [DInterval] [863, 867]: ok={ok_hd}, gap=[{gap_hdiv.lo}, {gap_hdiv.hi}]")
    assert ok_hd

    print("\n=== 5. Multi-Particle (k = 2, 3, 4) UFD Cluster Hybrid Certification on [691, 863] (B_hybrid^FJ = 691, discrete D <= 651, prime/all-fundamental D <= 643) ===")
    for d in range(831, 863, 4):
        ok_k3, gap_k3, _, det_k3 = certify_hybrid_k3_interval(d, d + 4, P_max=8999999, K=23, c_R_num=14, eps_J_num=56, Q_guar=750000, cls=vjd.FInterval, use_k4=False)
        print(f"  [FInterval P_max=9M]   [{d}, {d+4}]: ok={ok_k3}, gap={gap_k3:+.6f}, ufd_save={det_k3['ufd_save']:.6f}, n_comp={det_k3['n_composites']}")
        assert ok_k3 and gap_k3 > 0.002
    ok_k3_831d, _, gap_k3_831div, _ = certify_hybrid_k3_interval(831, 835, P_max=8999999, K=23, c_R_num=14, eps_J_num=56, Q_guar=750000, cls=vjd.DInterval, use_k4=False)
    print(f"  [DInterval P_max=9M]   [831, 835]: ok={ok_k3_831d}, gap=[{gap_k3_831div.lo}, {gap_k3_831div.hi}]")
    assert ok_k3_831d

    for d in range(755, 831, 4):
        ok_k3, gap_k3, _, det_k3 = certify_hybrid_k3_interval(d, d + 4, P_max=36000000, K=19, c_R_num=13, eps_J_num=60, Q_guar=3600000, cls=vjd.FInterval, use_k4=False)
        print(f"  [FInterval P_max=36M]  [{d}, {d+4}]: ok={ok_k3}, gap={gap_k3:+.6f}, ufd_save={det_k3['ufd_save']:.6f}, n_comp={det_k3['n_composites']}")
        assert ok_k3 and gap_k3 > 0.0008
    ok_k3_755d, _, gap_k3_755div, _ = certify_hybrid_k3_interval(755, 759, P_max=36000000, K=19, c_R_num=13, eps_J_num=60, Q_guar=3600000, cls=vjd.DInterval, use_k4=False)
    print(f"  [DInterval P_max=36M]  [755, 759]: ok={ok_k3_755d}, gap=[{gap_k3_755div.lo}, {gap_k3_755div.hi}]")
    assert ok_k3_755d

    for d in range(731, 755, 4):
        ok_k3_78, gap_k3_78, _, det_k3_78 = certify_hybrid_k3_interval(d, d + 4, P_max=78000000, K=19, c_R_num=13, eps_J_num=60, Q_guar=6100000, cls=vjd.FInterval, M_min_cache=178, use_k4=False)
        print(f"  [FInterval P_max=78M]  [{d}, {d+4}]: ok={ok_k3_78}, gap={gap_k3_78:+.6f}, ufd_save={det_k3_78['ufd_save']:.6f}, n_comp={det_k3_78['n_composites']}")
        assert ok_k3_78 and gap_k3_78 > 0.003
    ok_k3_731d, _, gap_k3_731div, _ = certify_hybrid_k3_interval(731, 735, P_max=78000000, K=19, c_R_num=13, eps_J_num=60, Q_guar=6100000, cls=vjd.DInterval, M_min_cache=178, use_k4=False)
    print(f"  [DInterval P_max=78M]  [731, 735]: ok={ok_k3_731d}, gap=[{gap_k3_731div.lo}, {gap_k3_731div.hi}]")
    assert ok_k3_731d

    ok_723f, gap_723f, _, det_723f = certify_hybrid_k3_interval(723, 723, P_max=78000000, K=19, c_R_num=13, eps_J_num=60, Q_guar=6100000, cls=vjd.FInterval, M_min_cache=178, use_k4=False)
    print(f"  [FInterval P_max=78M]  D_0 = 723 (3 mod 8): ok={ok_723f}, gap={gap_723f:+.6f}, ufd_save={det_723f['ufd_save']:.6f}, n_comp={det_723f['n_composites']}")
    assert ok_723f and gap_723f > 0.003
    ok_723d, _, gap_723div, _ = certify_hybrid_k3_interval(723, 723, P_max=78000000, K=19, c_R_num=13, eps_J_num=60, Q_guar=6100000, cls=vjd.DInterval, M_min_cache=178, use_k4=False)
    print(f"  [DInterval P_max=78M]  D_0 = 723 (3 mod 8): ok={ok_723d}, gap=[{gap_723div.lo}, {gap_723div.hi}]")
    assert ok_723d

    for d in range(715, 731, 4):
        ok_k3, gap_k3, _, det_k3 = certify_hybrid_k3_interval(d, d + 4, P_max=169000000, K=19, c_R_num=12, eps_J_num=64, Q_guar=13000000, cls=vjd.FInterval, M_min_cache=167, use_k4=False)
        print(f"  [FInterval P_max=169M] [{d}, {d+4}]: ok={ok_k3}, gap={gap_k3:+.6f}, ufd_save={det_k3['ufd_save']:.6f}, n_comp={det_k3['n_composites']}")
        assert ok_k3 and gap_k3 > 0.004
    ok_d715, _, gap_d715, _ = certify_hybrid_k3_interval(715, 719, P_max=169000000, K=19, c_R_num=12, eps_J_num=64, Q_guar=13000000, cls=vjd.DInterval, M_min_cache=167, use_k4=False)
    print(f"  [DInterval P_max=169M] [715, 719]: ok={ok_d715}, gap=[{gap_d715.lo}, {gap_d715.hi}]")
    assert ok_d715

    for d in [699, 703, 707, 711]:
        ok_k3, gap_k3, _, det_k3 = certify_hybrid_k3_interval(d, d + 4, P_max=312000000, K=19, c_R_num=12, eps_J_num=64, Q_guar=24000000, cls=vjd.FInterval, M_min_cache=159, use_k4=False)
        print(f"  [FInterval P_max=312M] [{d}, {d+4}]: ok={ok_k3}, gap={gap_k3:+.6f}, G={det_k3['G']}, ufd_save={det_k3['ufd_save']:.6f}, n_comp={det_k3['n_composites']}")
        assert ok_k3 and gap_k3 > 0.0015
    ok_d707, _, gap_d707, _ = certify_hybrid_k3_interval(707, 711, P_max=312000000, K=19, c_R_num=12, eps_J_num=64, Q_guar=24000000, cls=vjd.DInterval, M_min_cache=159, use_k4=False)
    print(f"  [DInterval P_max=312M] [707, 711]: ok={ok_d707}, gap=[{gap_d707.lo}, {gap_d707.hi}]")
    assert ok_d707
    ok_d699_312, _, gap_d699_312, _ = certify_hybrid_k3_interval(699, 703, P_max=312000000, K=19, c_R_num=12, eps_J_num=64, Q_guar=24000000, cls=vjd.DInterval, M_min_cache=159, use_k4=False)
    print(f"  [DInterval P_max=312M] [699, 703]: ok={ok_d699_312}, gap=[{gap_d699_312.lo}, {gap_d699_312.hi}]")
    assert ok_d699_312

    for d0 in [699, 691, 683]:
        ok_k3, gap_k3, _, det_k3 = certify_hybrid_k3_interval(d0, d0, P_max=312000000, K=19, c_R_num=12, eps_J_num=64, Q_guar=24000000, cls=vjd.FInterval, M_min_cache=159, use_k4=False)
        print(f"  [FInterval P_max=312M] D_0 = {d0}: ok={ok_k3}, gap={gap_k3:+.6f}, G={det_k3['G']}, ufd_save={det_k3['ufd_save']:.6f}, n_comp={det_k3['n_composites']}")
        assert ok_k3 and gap_k3 > 0.003
    ok_d691, _, gap_d691, _ = certify_hybrid_k3_interval(691, 691, P_max=312000000, K=19, c_R_num=12, eps_J_num=64, Q_guar=24000000, cls=vjd.DInterval, M_min_cache=159, use_k4=False)
    print(f"  [DInterval P_max=312M] D_0 = 691: ok={ok_d691}, gap=[{gap_d691.lo}, {gap_d691.hi}]")
    assert ok_d691
    ok_d683, _, gap_d683, _ = certify_hybrid_k3_interval(683, 683, P_max=312000000, K=19, c_R_num=12, eps_J_num=64, Q_guar=24000000, cls=vjd.DInterval, M_min_cache=159, use_k4=False)
    print(f"  [DInterval P_max=312M] D_0 = 683: ok={ok_d683}, gap=[{gap_d683.lo}, {gap_d683.hi}]")
    assert ok_d683

    for d in [691, 695, 699, 703]:
        ok_k3, gap_k3, _, det_k3 = certify_hybrid_k3_interval(d, d + 4, P_max=756000000, K=19, c_R_num=12, eps_J_num=63, Q_guar=56000000, cls=vjd.FInterval, M_min_cache=153, use_k4=True)
        print(f"  [FInterval P_max=756M] [{d}, {d+4}]: ok={ok_k3}, gap={gap_k3:+.6f}, G={det_k3['G']}, ufd_save={det_k3['ufd_save']:.6f} (save_k2={det_k3['save_k2']:.6f}, save_k3={det_k3['save_k3']:.6f}, save_k4={det_k3['save_k4']:.2e}), n_comp={det_k3['n_composites']}")
        assert ok_k3 and gap_k3 > 0.009 and det_k3["save_k4"] == 0.0
    ok_d699, _, gap_d699, _ = certify_hybrid_k3_interval(699, 703, P_max=756000000, K=19, c_R_num=12, eps_J_num=63, Q_guar=56000000, cls=vjd.DInterval, M_min_cache=153, use_k4=True)
    print(f"  [DInterval P_max=756M] [699, 703]: ok={ok_d699}, gap=[{gap_d699.lo}, {gap_d699.hi}]")
    assert ok_d699
    ok_d691_756, _, gap_d691_756, _ = certify_hybrid_k3_interval(691, 695, P_max=756000000, K=19, c_R_num=12, eps_J_num=63, Q_guar=56000000, cls=vjd.DInterval, M_min_cache=153, use_k4=True)
    print(f"  [DInterval P_max=756M] [691, 695]: ok={ok_d691_756}, gap=[{gap_d691_756.lo}, {gap_d691_756.hi}]")
    assert ok_d691_756

    for d0 in [667, 659]:
        ok_k3, gap_k3, _, det_k3 = certify_hybrid_k3_interval(d0, d0, P_max=756000000, K=19, c_R_num=12, eps_J_num=63, Q_guar=56000000, cls=vjd.FInterval, M_min_cache=153, use_k4=True, clamp_m3=False)
        print(f"  [FInterval P_max=756M] D_0 = {d0}: ok={ok_k3}, gap={gap_k3:+.6f}, G={det_k3['G']}, ufd_save={det_k3['ufd_save']:.6f} (save_k2={det_k3['save_k2']:.6f}, save_k3={det_k3['save_k3']:.6f}, save_k4={det_k3['save_k4']:.2e}), n_comp={det_k3['n_composites']}")
        assert ok_k3 and gap_k3 > 0.0008
        if d0 == 667:
            assert det_k3["save_k4"] == 0.0
        else:
            assert 6.0e-9 < det_k3["save_k4"] < 7.0e-9
    ok_d667, _, gap_d667, _ = certify_hybrid_k3_interval(667, 667, P_max=756000000, K=19, c_R_num=12, eps_J_num=63, Q_guar=56000000, cls=vjd.DInterval, M_min_cache=153, use_k4=True, clamp_m3=False)
    print(f"  [DInterval P_max=756M] D_0 = 667: ok={ok_d667}, gap=[{gap_d667.lo}, {gap_d667.hi}]")
    assert ok_d667
    ok_d659, _, gap_d659, _ = certify_hybrid_k3_interval(659, 659, P_max=756000000, K=19, c_R_num=12, eps_J_num=63, Q_guar=56000000, cls=vjd.DInterval, M_min_cache=153, use_k4=True, clamp_m3=False)
    print(f"  [DInterval P_max=756M] D_0 = 659: ok={ok_d659}, gap=[{gap_d659.lo}, {gap_d659.hi}]")
    assert ok_d659

    print("\n=== 6. Node-Block Fischer + Meixner/Composition/Schur Hybrid Certification on [551, 691] and Discrete D_0 down to 515 (B_hybrid^MS = 551 width-4, fundamental & prime/all-h(-D)=1 D <= 499) ===")
    for cls_ms in (vjd.FInterval, vjd.DInterval):
        eps_643_iv = cls_ms(57153599) / cls_ms(907199992)
        theta_643_iv = cls_ms(5414551596852631) / cls_ms(10831087100731600)
        eta_643_iv = cls_ms(1789913076568403) / cls_ms(15568502080706361344)
        L_643_iv = cls_ms(2350827399855823) / cls_ms(562949953421312)
        ub_mira_643 = compute_meixner_schur_var_ub_iv(
            cls_ms, 907199992, 47747368, 19, 57153599, 907199992,
            eps_643_iv, theta_643_iv, eta_643_iv, L_643_iv,
            A_num=3, A_den=25, v_num=4, v_den=5, beta_num=-1, beta_den=4, dual_num=135, dual_den=1000,
        )
        ub_opt_643 = compute_meixner_schur_var_ub_iv(
            cls_ms, 907199992, 47747368, 19, 57153599, 907199992,
            eps_643_iv, theta_643_iv, eta_643_iv, L_643_iv,
        )
        assert float(ub_mira_643.lo) >= 0.19980799219893585 and float(ub_mira_643.hi) <= 0.19980800
        assert float(ub_opt_643.hi) <= 0.19453710
    print(f"  [Meixner/Schur D=643 Benchmark Audit] mira_cairn [16, 21] contract: DInterval=[{ub_mira_643.lo}, {ub_mira_643.hi}], opt (9/200, 93/100, -3/5, 19/200): DInterval=[{ub_opt_643.lo}, {ub_opt_643.hi}]")

    # 6A. Resultant K=19 Meixner/Schur baseline at P_max=756M (reusing hot P_max=756M, M_min=153 cache from Section 5)
    for d in [647, 651]:
        ok_ms, gap_ms, _, det_ms = certify_hybrid_k3_interval(
            d, d + 4, P_max=756000000, K=19, c_R_num=12, eps_J_num=63, Q_guar=56000000,
            cls=vjd.FInterval, M_min_cache=153, use_k4=True, use_meixner_schur=True,
        )
        print(f"  [FInterval K=19 MS P_max=756M] [{d}, {d+4}]: ok={ok_ms}, gap={gap_ms:+.6f}, G={det_ms['G']}, ufd_save={det_ms['ufd_save']:.6f}, n_comp={det_ms['n_composites']}")
        assert ok_ms and gap_ms > 0.010
    ok_d647_651, _, gap_d647_651, _ = certify_hybrid_k3_interval(
        647, 651, P_max=756000000, K=19, c_R_num=12, eps_J_num=63, Q_guar=56000000,
        cls=vjd.DInterval, M_min_cache=153, use_k4=True, use_meixner_schur=True,
    )
    print(f"  [DInterval K=19 MS P_max=756M] [647, 651]: ok={ok_d647_651}, gap=[{gap_d647_651.lo}, {gap_d647_651.hi}]")
    assert ok_d647_651

    for d0 in [643, 627, 619, 611]:
        ok_ms0, gap_ms0, _, det_ms0 = certify_hybrid_k3_interval(
            d0, d0, P_max=756000000, K=19, c_R_num=12, eps_J_num=63, Q_guar=56000000,
            cls=vjd.FInterval, M_min_cache=153, use_k4=True, clamp_m3=False, use_meixner_schur=True,
        )
        print(f"  [FInterval K=19 MS P_max=756M] D_0 = {d0}: ok={ok_ms0}, gap={gap_ms0:+.6f}, G={det_ms0['G']}, ufd_save={det_ms0['ufd_save']:.6f}, n_comp={det_ms0['n_composites']}")
        assert ok_ms0 and gap_ms0 > 0.004
    for d0_dec in [643, 619, 611]:
        ok_ms_d, _, gap_ms_d, _ = certify_hybrid_k3_interval(
            d0_dec, d0_dec, P_max=756000000, K=19, c_R_num=12, eps_J_num=63, Q_guar=56000000,
            cls=vjd.DInterval, M_min_cache=153, use_k4=True, clamp_m3=False, use_meixner_schur=True,
        )
        print(f"  [DInterval K=19 MS P_max=756M] D_0 = {d0_dec}: ok={ok_ms_d}, gap=[{gap_ms_d.lo}, {gap_ms_d.hi}]")
        assert ok_ms_d

    # 6B. Wronskian Rank (Lemma 3.4 / [23, Thm 2.1]) + High-theta Meixner/Schur (K=43, c_R=1.2, eps_J=0.125, theta~0.8333)
    #     across [579, 691] at P_max=36M, [551, 579] and D_0=547 at P_max=169M, and D_0 in {587, 547, 523, 515} at P_max=312M & 756M
    ms_wron_p = (40, 200, 70, 100, -4, 5, 12, 200)
    P_36 = 36000000
    J_36 = (125 * 43 * ((12 * P_36) // (10 * 43))) // 1000
    min_36_gap = 1e9
    for d in range(579, 691, 4):
        ok_w36, gap_w36, _, det_w36 = certify_hybrid_k3_interval(
            d, d + 4, P_max=P_36, K=43, c_R_num=12, eps_J_num=125, Q_guar=J_36,
            cls=vjd.FInterval, M_min_cache=145, use_k4=False, clamp_m3=False,
            use_meixner_schur=True, use_wronskian=True, ms_params=ms_wron_p,
        )
        assert ok_w36 and gap_w36 > 0.030
        if gap_w36 < min_36_gap:
            min_36_gap = gap_w36
        if d in (579, 583, 587, 647, 687):
            ok_w36_d, _, gap_w36_div, _ = certify_hybrid_k3_interval(
                d, d + 4, P_max=P_36, K=43, c_R_num=12, eps_J_num=125, Q_guar=J_36,
                cls=vjd.DInterval, M_min_cache=145, use_k4=False, clamp_m3=False,
                use_meixner_schur=True, use_wronskian=True, ms_params=ms_wron_p,
            )
            assert ok_w36_d
            print(f"  [Wronskian K=43 MS P_max=36M]  [{d}, {d+4}]: FInterval={gap_w36:+.6f} | DInterval=[{gap_w36_div.lo}, {gap_w36_div.hi}]")
    print(f"  [Wronskian K=43 MS P_max=36M]  All 28 contiguous width-4 intervals in [579, 691] certified! Min gap={min_36_gap:+.6f}")

    P_169 = 169000000
    J_169 = (125 * 43 * ((12 * P_169) // (10 * 43))) // 1000
    for d in range(551, 579, 4):
        ok_w169, gap_w169, _, det_w169 = certify_hybrid_k3_interval(
            d, d + 4, P_max=P_169, K=43, c_R_num=12, eps_J_num=125, Q_guar=J_169,
            cls=vjd.FInterval, M_min_cache=137, use_k4=False, clamp_m3=False,
            use_meixner_schur=True, use_wronskian=True, ms_params=ms_wron_p,
        )
        assert ok_w169 and gap_w169 > 0.014
        if d in (551, 555, 575):
            ok_w169_d, _, gap_w169_div, _ = certify_hybrid_k3_interval(
                d, d + 4, P_max=P_169, K=43, c_R_num=12, eps_J_num=125, Q_guar=J_169,
                cls=vjd.DInterval, M_min_cache=137, use_k4=False, clamp_m3=False,
                use_meixner_schur=True, use_wronskian=True, ms_params=ms_wron_p,
            )
            assert ok_w169_d
            print(f"  [Wronskian K=43 MS P_max=169M] [{d}, {d+4}]: FInterval={gap_w169:+.6f} | DInterval=[{gap_w169_div.lo}, {gap_w169_div.hi}]")
        else:
            print(f"  [Wronskian K=43 MS P_max=169M] [{d}, {d+4}]: FInterval={gap_w169:+.6f}, G={det_w169['G']}, ufd_save={det_w169['ufd_save']:.6f}")
    ok_547_169, gap_547_169, _, _ = certify_hybrid_k3_interval(
        547, 547, P_max=P_169, K=43, c_R_num=12, eps_J_num=125, Q_guar=J_169,
        cls=vjd.FInterval, M_min_cache=137, use_k4=False, clamp_m3=False,
        use_meixner_schur=True, use_wronskian=True, ms_params=ms_wron_p,
    )
    ok_547_169d, _, gap_547_169div, _ = certify_hybrid_k3_interval(
        547, 547, P_max=P_169, K=43, c_R_num=12, eps_J_num=125, Q_guar=J_169,
        cls=vjd.DInterval, M_min_cache=137, use_k4=False, clamp_m3=False,
        use_meixner_schur=True, use_wronskian=True, ms_params=ms_wron_p,
    )
    assert ok_547_169 and ok_547_169d and gap_547_169 > 0.047
    print(f"  [Wronskian K=43 MS P_max=169M] D_0 = 547: FInterval={gap_547_169:+.6f} | DInterval=[{gap_547_169div.lo}, {gap_547_169div.hi}]")

    P_312 = 312000000
    J_312 = (125 * 43 * ((12 * P_312) // (10 * 43))) // 1000
    for d0 in [547, 523, 515]:
        ok_w312, gap_w312, _, det_w312 = certify_hybrid_k3_interval(
            d0, d0, P_max=P_312, K=43, c_R_num=12, eps_J_num=125, Q_guar=J_312,
            cls=vjd.FInterval, M_min_cache=129, use_k4=False, clamp_m3=False,
            use_meixner_schur=True, use_wronskian=True, ms_params=ms_wron_p,
        )
        ok_w312_d, _, gap_w312_div, _ = certify_hybrid_k3_interval(
            d0, d0, P_max=P_312, K=43, c_R_num=12, eps_J_num=125, Q_guar=J_312,
            cls=vjd.DInterval, M_min_cache=129, use_k4=False, clamp_m3=False,
            use_meixner_schur=True, use_wronskian=True, ms_params=ms_wron_p,
        )
        assert ok_w312 and ok_w312_d and gap_w312 > 0.0006
        print(f"  [Wronskian K=43 MS P_max=312M] D_0 = {d0}: FInterval={gap_w312:+.6f} | DInterval=[{gap_w312_div.lo}, {gap_w312_div.hi}]")

    P_756 = 756000000
    J_756 = (125 * 43 * ((12 * P_756) // (10 * 43))) // 1000
    for d0 in [587, 547, 523, 515]:
        ok_w756, gap_w756, _, det_w756 = certify_hybrid_k3_interval(
            d0, d0, P_max=P_756, K=43, c_R_num=12, eps_J_num=125, Q_guar=J_756,
            cls=vjd.FInterval, M_min_cache=129, use_k4=True, clamp_m3=False,
            use_meixner_schur=True, use_wronskian=True, ms_params=ms_wron_p,
        )
        ok_w756_d, _, gap_w756_div, _ = certify_hybrid_k3_interval(
            d0, d0, P_max=P_756, K=43, c_R_num=12, eps_J_num=125, Q_guar=J_756,
            cls=vjd.DInterval, M_min_cache=129, use_k4=True, clamp_m3=False,
            use_meixner_schur=True, use_wronskian=True, ms_params=ms_wron_p,
        )
        assert ok_w756 and ok_w756_d and gap_w756 > 0.041
        print(f"  [Wronskian K=43 MS P_max=756M] D_0 = {d0}: FInterval={gap_w756:+.6f} | DInterval=[{gap_w756_div.lo}, {gap_w756_div.hi}]")

    print(f"\nALL 6 EULER-WINDOW, FUBINI-JENSEN (B_hybrid^FJ = 691 / 659) & WRONSKIAN-MEIXNER-SCHUR (B_hybrid^MS = 551 / D <= 499) CERTIFICATIONS PASSED in {time.time() - t0:.2f}s.")


if __name__ == "__main__":
    main()
