"""Numerical support for the determinant comparison. Source history is in the paper.

Retained function bodies are unchanged. Unused top-level functions and the
standalone historical demonstration are omitted. See ../README.md for scope.
"""
import sys
import math
import bisect

import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import verify_jet_disk as vjd


def solve_variational_fubini_jensen_iv(
    M_steps: int,
    N_num: int,
    D_den: int,
    K: int,
    rho_n_lo_iv,
    base_rad_lo_iv,
    delta_D_lo_iv,
    rho_n_hi_iv,
    base_rad_hi_iv,
    delta_D_hi_iv,
    n: int,
    R: int,
    J: int,
    slope_j_lo_iv,
    cls=vjd.FInterval,
    b0_frac: float = 0.50,
    L_blocks: int = 320,
    J_quad: int | None = None,
    tail_mode: bool = False,
    theta_ub_iv=None,
):
    """
    Rigorous directed-rounding interval certification (FInterval or 26-digit DInterval)
    of the Fubini-Jensen C^1 Level-Set Convex Functional F_fubini_lb(w*).
    Supports both finite intervals (tail_mode=False) and the analytical infinite tail [D_lo, infty) (tail_mode=True).
    """
    M_tri = N_num
    S_int = R // K
    j_q = J if J_quad is None else J_quad
    theta_flt = float(N_num) / float(M_steps * D_den)
    theta_scale_flt = (theta_flt / float(theta_ub_iv.hi)) if (tail_mode and theta_ub_iv is not None) else 1.0
    u0_joint_flt = float(J + 2) / float(R)
    scale_K_flt = float(K - 1) / float(K)
    rho_flt = round(float(rho_n_hi_iv.lo), 5)
    brad_flt = round(float(base_rad_hi_iv.hi), 5)
    dd_flt = round(float(delta_D_hi_iv.hi), 5)
    slope_j_flt = round(float(slope_j_lo_iv.lo), 5)
    exp_neg_slope_flt = math.exp(-slope_j_flt)

    def B_joint_flt(G: float) -> float:
        if G <= 1.0 / K:
            u = math.sqrt(max(0.0, G / K))
        else:
            u = 1.0 - math.sqrt(max(0.0, scale_K_flt * (1.0 - G)))
        return 3.0 * max(0.0, u - u0_joint_flt)

    L_flt = [0.0] * (M_steps + 1)
    for b in range(M_steps):
        p_frac = min(1.0, (b + 1.0) / M_steps + 1.0 / n)
        r_b = math.sqrt(p_frac) * brad_flt + dd_flt
        L_flt[b] = math.log(rho_flt / r_b)
    dL_flt = [max(0.0, L_flt[b] - L_flt[b + 1]) for b in range(M_steps)]
    b0 = int(b0_frac * M_steps)
    pref_flt = 1.5 * (float(j_q) / float(R)) / theta_flt

    J_grid = (j_q + 1) if tail_mode else J
    m_knots = [int(round(r * (J_grid - 1) / float(L_blocks))) for r in range(L_blocks + 1)]
    blocks_int = []
    blocks_flt = []
    for r in range(L_blocks):
        m_lo = m_knots[r] + 1
        m_hi = m_knots[r + 1]
        if m_lo <= m_hi:
            cnt = m_hi - m_lo + 1
            blocks_int.append((cnt, m_lo, m_hi))
            tau_0_raw = (m_lo - 1) / float(J_grid)
            tau_1_raw = m_hi / float(J_grid)
            tau_0 = theta_scale_flt * tau_0_raw
            tau_1 = theta_scale_flt * tau_1_raw
            dtau = tau_1 - tau_0
            if tail_mode:
                G0_lo = 1.0 - (tau_1_raw + 1.0 / float(J_grid)) / theta_flt
                c_hi = (float(J) / float(R)) * (1.0 - tau_0_raw)
            else:
                G0_lo = 1.0 - (n * m_hi) / float(M_tri)
                c_hi = (J - m_lo) / float(R)
            blocks_flt.append((cnt, tau_0, tau_1, dtau, G0_lo, c_hi))

    def q_r_flt(w: float, tau_0: float, tau_1: float, dtau: float) -> float:
        if w <= tau_0:
            return 0.5 * (tau_0 + tau_1) - w
        if w >= tau_1:
            return 0.0
        diff = tau_1 - w
        return (diff * diff) / (2.0 * dtau)

    def dpsi_block_flt(D_frac: float, G0_lo: float, c_hi: float) -> float:
        G_end = G0_lo + D_frac
        if G_end <= max(0.0, G0_lo):
            return 0.0
        G_c = min(1.0, G_end)
        u = 1.0 - math.sqrt(max(0.0, 1.0 - G_c))
        if u <= c_hi + exp_neg_slope_flt:
            return 0.0
        return slope_j_flt + math.log(u - c_hi)

    w_flt = [theta_flt] * M_steps
    target_sum_flt = theta_flt * M_steps
    L_b = len(blocks_flt)
    taus_ext = [0.0] + [b[2] for b in blocks_flt] + [1.0]

    scale_fub_flt = 1.0 if tail_mode else (float(S_int + 1) / float(S_int))

    kw_cache = getattr(vjd, "_FJ_KW_CACHE", None)
    if kw_cache is None:
        kw_cache = {}
        vjd._FJ_KW_CACHE = kw_cache
    sl_key = (round(slope_j_flt, 5), round(rho_flt, 5), round(brad_flt, 5), round(dd_flt, 5)) if tail_mode else (
        round(slope_j_flt, 2) if K == 29 else (round(slope_j_flt, 5), round(rho_flt, 3))
    )
    kw_key = (M_steps, N_num, D_den, K, n, R, J, sl_key, b0_frac, L_blocks, tail_mode)
    warm_key = ("warm", M_steps, K, b0_frac, L_blocks) if (not tail_mode and K == 29 and R > 400000) else None
    if kw_key in kw_cache:
        k_w = list(kw_cache[kw_key])
    else:
        if warm_key is not None and warm_key in kw_cache:
            wn_prev, mu_prev = kw_cache[warm_key]
            w_flt = [min(1.0, max(0.0, wn * theta_flt)) for wn in wn_prev]
            n_iters = 8
        else:
            mu_prev = 0.5
            n_iters = 50
        for it in range(n_iters):
            G_flt = [0.0] * M_steps
            s_acc = 0.0
            for b in range(M_steps):
                s_acc += w_flt[b] / target_sum_flt
                G_flt[b] = min(1.0, s_acc)
            suff = [0.0] * M_steps
            acc = 0.0
            for b in range(M_steps - 1, -1, -1):
                acc += dL_flt[b] * B_joint_flt(G_flt[b]) / theta_flt
                suff[b] = acc
            w_sorted = sorted(w_flt)
            pref_w_flt = [0.0] * (M_steps + 1)
            for i_w in range(M_steps):
                pref_w_flt[i_w + 1] = pref_w_flt[i_w] + w_sorted[i_w]
            dpsi_w = []
            for cnt, tau_0, tau_1, dtau, G0_lo, c_hi in blocks_flt:
                i0 = bisect.bisect_right(w_sorted, tau_0)
                i1 = bisect.bisect_left(w_sorted, tau_1)
                sum_q = i0 * (0.5 * (tau_0 + tau_1)) - pref_w_flt[i0]
                inv_2dtau = 1.0 / (2.0 * dtau)
                for i_w in range(i0, i1):
                    diff = tau_1 - w_sorted[i_w]
                    sum_q += (diff * diff) * inv_2dtau
                D_frac = sum_q / target_sum_flt
                dpsi_w.append(dpsi_block_flt(D_frac, G0_lo, c_hi) * scale_fub_flt * (cnt / float(J_grid)))
            S_knots = [0.0] * (L_b + 2)
            cur_s = 0.0
            for r in range(L_b - 1, -1, -1):
                cur_s += dpsi_w[r]
                S_knots[r] = cur_s

            Lb0 = max(1e-9, L_flt[b0])
            yb_b0 = [Lb0 * taus_ext[r] - S_knots[r] for r in range(L_b + 2)]
            yb_by_b = [yb_b0] * (b0 + 1)
            for b in range(b0 + 1, M_steps):
                Lb = max(1e-9, L_flt[b])
                yb_by_b.append([Lb * taus_ext[r] - S_knots[r] for r in range(L_b + 2)])
            inv_2pref_flt = 1.0 / (2.0 * pref_flt)

            def solve_wb(b: int, rhs: float) -> float:
                y = rhs * inv_2pref_flt
                yb = yb_by_b[b]
                if y <= yb[0]:
                    return 0.0
                if y >= yb[-1]:
                    return 1.0
                idx = min(L_b, max(0, bisect.bisect_right(yb, y) - 1))
                w0, w1 = taus_ext[idx], taus_ext[idx + 1]
                y0, y1 = yb[idx], yb[idx + 1]
                if y1 <= y0:
                    return w0
                return min(1.0, max(0.0, w0 + (y - y0) / (y1 - y0) * (w1 - w0)))

            if n_iters == 8:
                lo_mu, hi_mu = mu_prev - 0.5, mu_prev + 0.5
                if sum(solve_wb(b, lo_mu - suff[b]) for b in range(M_steps)) >= target_sum_flt:
                    lo_mu = -10.0
                if sum(solve_wb(b, hi_mu - suff[b]) for b in range(M_steps)) <= target_sum_flt:
                    hi_mu = 10.0
                n_bisect = 18
                step = 0.25 if it < 4 else 0.12
            else:
                lo_mu, hi_mu = -10.0, 10.0
                n_bisect = 30
                step = 0.35 if it < 30 else 0.12
            for _ in range(n_bisect):
                mu = 0.5 * (lo_mu + hi_mu)
                if sum(solve_wb(b, mu - suff[b]) for b in range(M_steps)) < target_sum_flt:
                    lo_mu = mu
                else:
                    hi_mu = mu
            mu = 0.5 * (lo_mu + hi_mu)
            mu_prev = mu
            for b in range(M_steps):
                w_flt[b] = (1.0 - step) * w_flt[b] + step * solve_wb(b, mu - suff[b])

        k_w = [min(D_den, max(0, int(round(w_flt[b] * D_den)))) for b in range(M_steps)]
        diff_k = N_num - sum(k_w)
        while diff_k != 0:
            if diff_k > 0:
                best_b = max((b for b in range(M_steps) if k_w[b] < D_den), key=lambda b: w_flt[b] * D_den - k_w[b])
                take = min(diff_k, D_den - k_w[best_b])
                k_w[best_b] += take
                diff_k -= take
            else:
                best_b = min((b for b in range(M_steps) if k_w[b] > 0), key=lambda b: w_flt[b] * D_den - k_w[b])
                take = min(-diff_k, k_w[best_b])
                k_w[best_b] -= take
                diff_k += take
        if len(kw_cache) >= 5000:
            kw_cache.clear()
        kw_cache[kw_key] = tuple(k_w)
        if warm_key is not None:
            kw_cache[warm_key] = (tuple(w / theta_flt for w in w_flt), mu_prev)

    # Exact directed-rounding interval certification at rational witness w*_b = k_w[b] / D_den
    iv_0, iv_1, iv_2, iv_3 = cls(0), cls(1), cls(2), cls(3)
    iv_half = iv_1 / iv_2
    iv_M, iv_K, iv_R, iv_J = cls(M_steps), cls(K), cls(R), cls(J)
    iv_J_grid = cls(J_grid)
    iv_N_num, iv_D_den = cls(N_num), cls(D_den)
    theta_iv = iv_N_num / (iv_M * iv_D_den)
    theta_scale_iv = (theta_iv / theta_ub_iv) if (tail_mode and theta_ub_iv is not None) else iv_1
    target_sum_iv = theta_iv * iv_M
    u0_joint_iv = cls(J + 2) / iv_R
    scale_K_iv = cls(K - 1) / iv_K
    inv_K_iv = iv_1 / iv_K
    W_main_iv = cls(R * R * S_int) / iv_3
    pref_iv = (iv_3 * (cls(j_q) / iv_R)) / (iv_2 * theta_iv)
    scale_fub_iv = iv_1 if tail_mode else (cls(S_int + 1) / cls(S_int))
    exp_neg_slope_iv = (iv_0 - slope_j_lo_iv).exp()

    def anti_q_iv(t_iv, u0_iv):
        t2 = t_iv * t_iv
        t3 = t2 * t_iv
        return ((iv_1 + u0_iv) / iv_2) * t2 - (t3 / iv_3) - u0_iv * t_iv

    anti_u0_joint_iv = anti_q_iv(u0_joint_iv, u0_joint_iv)

    L_iv = [iv_0] * (M_steps + 1)
    for b in range(M_steps):
        p_frac_iv = vjd.ival_min(iv_1, cls(b + 1) / iv_M + iv_1 / cls(n), cls)
        r_b_iv = p_frac_iv.sqrt() * base_rad_hi_iv + delta_D_hi_iv
        L_iv[b] = (rho_n_hi_iv / r_b_iv).ln()
    dL_iv = [vjd.ival_max(iv_0, L_iv[b] - L_iv[b + 1], cls) for b in range(M_steps)]

    if tail_mode:
        p_frac_b0_lo = cls(b0 + 1) / iv_M
        L_b0_hi_iv = (iv_1 / p_frac_b0_lo).ln() / iv_2
    else:
        p_frac_b0_iv = vjd.ival_min(iv_1, cls(b0 + 1) / iv_M + iv_1 / cls(n), cls)
        r_b0_lo_iv = p_frac_b0_iv.sqrt() * base_rad_lo_iv + delta_D_lo_iv
        L_b0_hi_iv = (rho_n_lo_iv / r_b0_lo_iv).ln()

    js_int = max(0, J - S_int)
    num_hockey = J * (J + 1) * (J + 2) - js_int * (js_int + 1) * (js_int + 2)
    Delta0_iv = cls(num_hockey) / (iv_3 * W_main_iv)

    w_iv = [cls(k_w[b]) / iv_D_den for b in range(M_steps)]
    k_w_sorted = sorted(k_w)
    w_sorted_iv = [cls(k) / iv_D_den for k in k_w_sorted]
    w_sorted_hi = [x.hi for x in w_sorted_iv]
    w_sorted_lo = [x.lo for x in w_sorted_iv]
    pref_k_w = [0] * (M_steps + 1)
    for i_w in range(M_steps):
        pref_k_w[i_w + 1] = pref_k_w[i_w] + k_w_sorted[i_w]

    G_iv = [iv_0] * M_steps
    k_acc = 0
    for b in range(M_steps):
        k_acc += k_w[b]
        G_iv[b] = cls(min(N_num, k_acc)) / iv_N_num

    B_G_iv = [iv_0] * M_steps
    Phi_G_iv = [iv_0] * M_steps
    for b in range(M_steps):
        Gb = G_iv[b]
        if Gb.hi <= inv_K_iv.lo:
            u_iv = (Gb / iv_K).sqrt()
        elif Gb.lo >= inv_K_iv.hi:
            u_iv = iv_1 - (scale_K_iv * vjd.ival_max(iv_0, iv_1 - Gb, cls)).sqrt()
        else:
            u_lo = (Gb / iv_K).sqrt()
            u_hi = iv_1 - (scale_K_iv * vjd.ival_max(iv_0, iv_1 - Gb, cls)).sqrt()
            u_iv = cls(u_lo.lo, u_hi.hi)
        B_G_iv[b] = iv_3 * vjd.ival_max(iv_0, u_iv - u0_joint_iv, cls)
        if u_iv.hi <= u0_joint_iv.lo:
            Phi_G_iv[b] = iv_0
        else:
            t_iv = vjd.ival_max(u0_joint_iv, u_iv, cls)
            Phi_G_iv[b] = iv_3 * (iv_2 / scale_K_iv) * vjd.ival_max(iv_0, anti_q_iv(t_iv, u0_joint_iv) - anti_u0_joint_iv, cls)

    def I_antideriv_iv(z_iv, c_iv):
        ln_z = z_iv.ln()
        term1 = iv_2 * (iv_1 - c_iv) * z_iv * (slope_j_lo_iv - iv_1 + ln_z)
        term2 = (z_iv * z_iv) * (slope_j_lo_iv - iv_half + ln_z)
        return term1 - term2

    F_lin_iv = iv_0
    F_quad_rad_iv = iv_0
    for b in range(M_steps):
        F_lin_iv = F_lin_iv + dL_iv[b] * Phi_G_iv[b]
        Lb = L_iv[max(b, b0)]
        wb = w_iv[b]
        F_quad_rad_iv = F_quad_rad_iv + ((pref_iv / iv_M) * Lb * (wb * wb))

    F_fub_iv = iv_0
    dpsi_w_iv = []
    block_params_iv = []
    tau0_lo_list = []
    tau1_hi_list = []
    for cnt, m_lo, m_hi in blocks_int:
        tau0_raw_iv = cls(m_lo - 1) / iv_J_grid
        tau1_raw_iv = cls(m_hi) / iv_J_grid
        dtau_raw_iv = cls(cnt) / iv_J_grid
        tau0_iv = theta_scale_iv * tau0_raw_iv
        tau1_iv = theta_scale_iv * tau1_raw_iv
        dtau_iv = theta_scale_iv * dtau_raw_iv
        mid_tau_iv = theta_scale_iv * (cls(m_lo - 1 + m_hi) / (iv_2 * iv_J_grid))
        if tail_mode:
            G0_lo_iv = iv_1 - (tau1_raw_iv + iv_1 / iv_J_grid) / theta_iv
            c_hi_iv = (iv_J / iv_R) * (iv_1 - tau0_raw_iv)
        else:
            G0_lo_iv = iv_1 - cls(n * m_hi) / cls(M_tri)
            c_hi_iv = cls(J - m_lo) / iv_R
        block_params_iv.append((tau0_iv, tau1_iv, dtau_iv))
        tau0_lo_list.append(tau0_iv.lo)
        tau1_hi_list.append(tau1_iv.hi)

        i0 = bisect.bisect_right(w_sorted_hi, tau0_iv.lo)
        i1 = bisect.bisect_left(w_sorted_lo, tau1_iv.hi)
        sum_q_iv = cls(i0) * mid_tau_iv - cls(pref_k_w[i0]) / iv_D_den
        for i_w in range(i0, i1):
            wb = w_sorted_iv[i_w]
            diff = vjd.ival_max(iv_0, tau1_iv - wb, cls)
            q_quad = (diff * diff) / (iv_2 * dtau_iv)
            if wb.lo >= tau0_iv.hi:
                sum_q_iv = sum_q_iv + q_quad
            else:
                q_lin = mid_tau_iv - wb
                sum_q_iv = sum_q_iv + cls(min(q_lin.lo, q_quad.lo), max(q_lin.hi, q_quad.hi))
        D_frac_iv = sum_q_iv / target_sum_iv
        u_min_iv = vjd.ival_min(iv_1, c_hi_iv + exp_neg_slope_iv, cls)
        G_min_iv = iv_1 - (iv_1 - u_min_iv) * (iv_1 - u_min_iv)
        G_start_iv = vjd.ival_max(G0_lo_iv, G_min_iv, cls)
        G_end_iv = vjd.ival_min(iv_1, G0_lo_iv + D_frac_iv, cls)
        if G_end_iv.hi <= G_start_iv.lo:
            dpsi_w_iv.append(iv_0)
        else:
            G_hi_iv = vjd.ival_max(G_start_iv, G_end_iv, cls)
            z_start_iv = vjd.ival_max(exp_neg_slope_iv, iv_1 - vjd.ival_max(iv_0, iv_1 - G_start_iv, cls).sqrt() - c_hi_iv, cls)
            z_hi_iv = vjd.ival_max(z_start_iv, iv_1 - vjd.ival_max(iv_0, iv_1 - G_hi_iv, cls).sqrt() - c_hi_iv, cls)
            psi_iv = vjd.ival_max(iv_0, I_antideriv_iv(z_hi_iv, c_hi_iv) - I_antideriv_iv(z_start_iv, c_hi_iv), cls)
            weight_r_iv = (iv_2 * theta_iv * pref_iv) * scale_fub_iv * dtau_raw_iv
            F_fub_iv = F_fub_iv + weight_r_iv * psi_iv
            dpsi_iv = vjd.ival_max(iv_0, slope_j_lo_iv + z_hi_iv.ln(), cls)
            dpsi_w_iv.append(dpsi_iv * scale_fub_iv * dtau_raw_iv)

    F_w_iv = F_lin_iv + F_quad_rad_iv + F_fub_iv - L_b0_hi_iv * Delta0_iv

    suff_dpsi_iv = [iv_0] * (L_b + 1)
    for r in range(L_b - 1, -1, -1):
        suff_dpsi_iv[r] = suff_dpsi_iv[r + 1] + dpsi_w_iv[r]

    grad_iv = [iv_0] * M_steps
    suff_iv = iv_0
    for b in range(M_steps - 1, -1, -1):
        suff_iv = suff_iv + (dL_iv[b] * B_G_iv[b]) / target_sum_iv
        Lb = L_iv[max(b, b0)]
        wb = w_iv[b]
        r0 = bisect.bisect_right(tau1_hi_list, wb.lo)
        r1 = bisect.bisect_left(tau0_lo_list, wb.hi)
        ramp_lin_iv = suff_dpsi_iv[r1]
        for r in range(r0, r1):
            dpsi_r = dpsi_w_iv[r]
            if dpsi_r.hi <= 0:
                continue
            tau0_iv, tau1_iv, dtau_iv = block_params_iv[r]
            if wb.hi <= tau0_iv.lo:
                dq_iv = iv_1
            elif wb.lo >= tau0_iv.hi:
                dq_iv = vjd.ival_min(iv_1, vjd.ival_max(iv_0, (tau1_iv - wb) / dtau_iv, cls), cls)
            else:
                dq_lo = vjd.ival_min(iv_1, vjd.ival_max(iv_0, (tau1_iv - wb) / dtau_iv, cls), cls).lo
                dq_iv = cls(dq_lo, iv_1.hi)
            ramp_lin_iv = ramp_lin_iv + dpsi_r * dq_iv
        grad_iv[b] = suff_iv + ((iv_2 * pref_iv) / iv_M) * (Lb * wb - ramp_lin_iv)

    idx_sorted = sorted(range(M_steps), key=lambda a: grad_iv[a].lo)
    k_vmin = [0] * M_steps
    rem_k = N_num
    for a in idx_sorted:
        take = min(D_den, rem_k)
        k_vmin[a] = take
        rem_k -= take
        if rem_k == 0:
            break

    sum_grad_w_hi = iv_0
    sum_grad_v_lo = iv_0
    for a in range(M_steps):
        if k_w[a] > 0:
            sum_grad_w_hi = sum_grad_w_hi + cls(grad_iv[a].hi, grad_iv[a].hi) * (cls(k_w[a]) / iv_D_den)
        if k_vmin[a] > 0:
            sum_grad_v_lo = sum_grad_v_lo + cls(grad_iv[a].lo, grad_iv[a].lo) * (cls(k_vmin[a]) / iv_D_den)
    duality_gap_ub = vjd.ival_max(iv_0, sum_grad_w_hi - sum_grad_v_lo, cls)
    F_rigorous_lb = F_w_iv - cls(duality_gap_ub.hi, duality_gap_ub.hi)
    return F_w_iv, cls(duality_gap_ub.hi, duality_gap_ub.hi), cls(F_rigorous_lb.lo, F_rigorous_lb.lo)


