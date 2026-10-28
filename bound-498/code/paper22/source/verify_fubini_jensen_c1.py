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


def certify_infinite_tail_fubini_jensen(
    D_lo: int = 5500000, K: int = 31, M_steps: int = 800, cls=vjd.FInterval, b0_frac: float = 0.48, eps_J_num: int = 60
):
    """
    Single-shot analytical proof that L_padic(D) > U_arch(D) for ALL real D >= D_lo,
    using the Fubini-Jensen C^1 Level-Set Convex Functional (tail_mode=True) and
    step-function Lebesgue integration for deriv_r_saving_lb.
    """
    iv_0, iv_1, iv_2, iv_3, iv_4 = cls(0), cls(1), cls(2), cls(3), cls(4)
    iv_K, iv_M = cls(K), cls(M_steps)
    pi_iv = (
        cls(vjd.Decimal("3.14159265358979323846264338"), vjd.Decimal("3.14159265358979323846264339"))
        if cls is vjd.DInterval
        else vjd.FInterval(math.pi)
    )
    sqrt3_iv = iv_3.sqrt()
    e_mertens_iv = (
        cls(vjd.Decimal("-1.33258227573322089"), vjd.Decimal("-1.33258227573322087"))
        if cls is vjd.DInterval
        else vjd.FInterval(vjd.E_MERTENS)
    )

    X_lo_iv = cls(D_lo - 3) / iv_4
    S_lo = (23 * (D_lo - 3)) // (40 * K)
    R_lo = K * S_lo
    J_lo = (eps_J_num * R_lo) // 1000
    iv_S, iv_R, iv_J = cls(S_lo), cls(R_lo), cls(J_lo)
    c_R_hi = cls(23) / cls(10)
    c_R_lo = c_R_hi - iv_K / X_lo_iv
    eps_J_hi = cls(eps_J_num) / cls(1000)
    eps_J_lo = eps_J_hi - iv_1 / iv_R

    ratio_My_S_ub = (
        iv_4 * ((cls(102) * iv_K) / (cls(100) * eps_J_lo)).sqrt() / (iv_2 * pi_iv * iv_S * cls(D_lo).sqrt()).sqrt()
        + (iv_1 + (iv_1 + iv_4 / cls(D_lo)).sqrt()) / iv_S
    )
    gamma_n_ub = iv_1 + ratio_My_S_ub + (cls(M_steps) * eps_J_hi) / iv_S
    assert float(gamma_n_ub.hi) <= 1.02
    gamma_n_lb = iv_1
    n_lo_raw = (R_lo * S_lo) // J_lo + 1
    n_lo = ((n_lo_raw + M_steps - 1) // M_steps) * M_steps

    D_den = 1000000
    N_num = int(float((iv_1 / (iv_2 * gamma_n_ub)).lo) * M_steps * D_den) - 1
    theta_lo = cls(N_num) / cls(M_steps * D_den)
    assert theta_lo.hi <= (iv_1 / (iv_2 * gamma_n_ub)).lo
    theta_ub = (iv_1 + iv_1 / iv_S) / (iv_2 * gamma_n_lb)
    nu_lo = (gamma_n_lb * c_R_lo) / (iv_K * eps_J_hi)
    nu_hi = (gamma_n_ub * c_R_hi) / (iv_K * eps_J_lo)

    eta_hi = (cls(D_lo + 4).sqrt() / iv_4) / ((nu_lo * X_lo_iv * cls(D_lo).sqrt()) / (iv_2 * pi_iv)).sqrt()
    C_rho_lo = (nu_lo / pi_iv).ln() / iv_2
    C_rho_hi = ((nu_hi * (iv_1 + iv_3 / (iv_4 * X_lo_iv)).sqrt()) / pi_iv).ln() / iv_2 + (iv_1 + eta_hi).ln()

    prime_powers_q0 = []
    for p in vjd.PRIMES:
        pk = p * p
        while pk <= 1000:
            prime_powers_q0.append((p, pk))
            pk *= p
    sigma2_q0_iv = iv_0
    for p, pk in prime_powers_q0:
        sigma2_q0_iv = sigma2_q0_iv + cls(p).ln() / cls(pk)

    logX_lo = X_lo_iv.ln()
    slope_j_lo = logX_lo / iv_4 + c_R_lo.ln() - C_rho_hi - sigma2_q0_iv
    slope_j_hi_at_Xlo = logX_lo / iv_4 + c_R_hi.ln() - C_rho_lo - sigma2_q0_iv

    const_j_ub = iv_0
    for p, pk in prime_powers_q0:
        cap_ratio = (iv_1 / (theta_lo * cls(pk))) * (iv_1 + cls(pk) / iv_J)
        b_full = min(pk, int(float((iv_1 / cap_ratio).lo)))
        r_rem = vjd.ival_max(iv_0, iv_1 - cls(b_full) * cap_ratio, cls)
        avg_frac = (
            cap_ratio * cls(b_full * (pk - 1) - (b_full * (b_full - 1)) // 2) / cls(pk)
            + r_rem * cls(max(0, pk - 1 - b_full)) / cls(pk)
        )
        const_j_ub = const_j_ub + iv_2 * avg_frac * cls(p).ln()

    # Exact step-function Lebesgue integration for deriv_r_saving_lb on [0, 1]:
    deriv_r_saving_lb = iv_0
    exp_neg_slope = (iv_0 - slope_j_lo).exp()
    M_tri_lo = R_lo * (S_lo + 1) // 2
    inv_M_tri_lo = iv_1 / cls(M_tri_lo)
    N_deriv = 3200
    iv_N_d = cls(N_deriv)
    for k_step in range(N_deriv):
        u_left = cls(k_step) / iv_N_d
        u_right = cls(k_step + 1) / iv_N_d
        one_m_ul = iv_1 - u_left
        one_m_ur = iv_1 - u_right
        one_m_ul_sq = one_m_ul * one_m_ul
        one_m_ur_sq = one_m_ur * one_m_ur
        j_low_u = vjd.ival_max(iv_0, (iv_1 - theta_ub * one_m_ul_sq) * eps_J_lo, cls)
        u_k_hi = iv_1 - vjd.ival_max(iv_0, one_m_ur_sq - inv_M_tri_lo, cls).sqrt()
        r_u = vjd.ival_min(iv_1, (iv_1 + iv_1 / iv_S) * u_k_hi + iv_1 / iv_R, cls)
        j_star = vjd.ival_max(iv_0, vjd.ival_min(j_low_u, r_u - exp_neg_slope, cls), cls)
        if j_star.hi <= 0:
            g_max = iv_0
        else:
            rem = r_u - j_star
            psi_int = r_u * r_u.ln() - rem * rem.ln() - j_star
            g_max = vjd.ival_max(iv_0, j_star * slope_j_lo + psi_int, cls)
        save_u = vjd.ival_max(iv_0, j_low_u * slope_j_lo - g_max, cls)
        weight_step = vjd.ival_max(iv_0, one_m_ul_sq - one_m_ur_sq, cls)
        deriv_r_saving_lb = deriv_r_saving_lb + weight_step * iv_3 * save_u

    J_hi_eff = (eps_J_num * R_lo) // 1000 + 1
    eps_J_eff = cls(J_hi_eff) / iv_R
    F_w_iv, dual_gap_iv, F_lb_iv = solve_variational_fubini_jensen_iv(
        M_steps,
        N_num,
        D_den,
        K,
        iv_1,
        iv_1,
        iv_0,
        iv_1 + eta_hi,
        iv_1,
        eta_hi,
        n_lo,
        R_lo,
        J_hi_eff,
        slope_j_lo,
        cls=cls,
        b0_frac=b0_frac,
        L_blocks=320,
        J_quad=J_lo - 1,
        tail_mode=True,
        theta_ub_iv=theta_ub,
    )
    unif_j_norm_ub = (
        (cls(3 * (S_lo + 1)) / cls(R_lo * S_lo)) * cls(J_hi_eff) * (iv_1 - theta_lo / iv_2)
        + (iv_3 * theta_ub * cls(J_hi_eff)) / cls(R_lo * R_lo * S_lo)
    )
    W12_norm_ub = iv_1 + iv_1 / iv_K + cls(3 * (K - 1)) / cls(2 * K * S_lo) + cls(max(0, K - 5)) / cls(2 * K * S_lo * S_lo)
    arch_at_Xlo = (
        W12_norm_ub * ((iv_3 / iv_4) * logX_lo + C_rho_hi)
        + unif_j_norm_ub * slope_j_hi_at_Xlo
        - F_lb_iv
        - deriv_r_saving_lb
        + (cls(3 * (S_lo + 1)) / cls(2 * R_lo * S_lo)) * const_j_ub
        + (cls(3 * (S_lo + 1)) / cls(R_lo * S_lo)) * cls(M_tri_lo).ln()
    )

    padic_at_Xlo = iv_0
    for p in vjd.PRIMES:
        if p >= K:
            break
        w_iv = vjd.exact_rigorous_W_biconj_tail_iv(p, K, S_lo, eps_J_eff, theta_lo, cls)
        padic_at_Xlo = padic_at_Xlo + w_iv * cls(p).ln()
    for p in vjd.PRIMES:
        if p < K:
            continue
        p_pow = p * p
        if p_pow > S_lo:
            break
        while p_pow <= S_lo:
            s_p2_lb = vjd.ival_max(
                iv_0,
                iv_1 / cls(K * p_pow)
                - cls(3) / cls(2 * R_lo)
                + cls(3) / cls(2 * R_lo * p_pow)
                - cls(p_pow) / (iv_2 * sqrt3_iv * iv_K * cls(S_lo ** 3)),
                cls,
            )
            padic_at_Xlo = padic_at_Xlo + s_p2_lb * cls(p).ln()
            p_pow *= (p * p)

    sum_small_K = iv_0
    for p in vjd.PRIMES:
        if p < K:
            sum_small_K = sum_small_K + cls(p).ln() / cls(p)
    sum_inv_p_lb = (logX_lo + e_mertens_iv - iv_1 / (iv_2 * logX_lo)) - sum_small_K
    floor_loss_ub = (cls(3) / (iv_2 * c_R_lo)) * (iv_1 + iv_1 / (iv_2 * logX_lo))
    u_lo = iv_1 / c_R_hi
    u_hi = iv_1 / c_R_lo
    bernoulli_lb = ((u_lo * u_lo) / iv_2 - (u_hi * u_hi * u_hi) / (cls(12) * sqrt3_iv)) * (
        (iv_1 - cls(3) / (iv_2 * logX_lo) - iv_1 / (iv_3 * logX_lo * logX_lo)) / iv_2
        - cls(160000) / (X_lo_iv * X_lo_iv)
    )
    padic_at_Xlo = padic_at_Xlo + sum_inv_p_lb - floor_loss_ub + bernoulli_lb
    gap_iv = padic_at_Xlo - arch_at_Xlo
    log_slope_iv = iv_1 - (iv_3 / iv_4) * W12_norm_ub - (iv_3 / iv_4) * unif_j_norm_ub
    details = {
        "D_lo": D_lo,
        "S": S_lo,
        "R": R_lo,
        "J": J_lo,
        "n": n_lo,
        "theta": float(theta_lo.lo),
        "slope_j": float(slope_j_lo.lo),
        "F_w": float(F_w_iv.lo),
        "duality_gap": float(dual_gap_iv.hi),
        "F_lb": float(F_lb_iv.lo),
        "save_deriv": float(deriv_r_saving_lb.lo),
        "U_arch": float(arch_at_Xlo.hi),
        "L_padic": float(padic_at_Xlo.lo),
        "gap": float(gap_iv.lo),
    }
    return gap_iv.lo > 0 and float(log_slope_iv.lo) > 0.12, float(gap_iv.lo), float(log_slope_iv.lo), gap_iv, details


if __name__ == "__main__":
    # 1. Verify at D = 3,968,539 in both FInterval and 26-digit DInterval
    for cls_name, cls in [("FInterval", vjd.FInterval), ("DInterval", vjd.DInterval)]:
        D_lo, D_hi = 3968539, 3970539
        P_max = (D_lo - 3) // 4
        K = 31
        M_steps = 800
        S = max(10, (23 * P_max) // (10 * K))
        R = K * S
        J = max(2, (58 * R) // 1000)
        M_tri = R * (S + 1) // 2
        delta_D_hi_flt = math.sqrt(D_hi + 4.0) / 4.0
        n = (R * S) // J + 1
        for _ in range(30):
            rho_n_hi_flt = math.sqrt(n * math.sqrt(D_hi) / (2.0 * math.pi)) + delta_D_hi_flt
            M_y_hi = 2 * int(2.0 * rho_n_hi_flt / math.sqrt(D_lo)) + 1
            n_req = (R * S + M_y_hi * R) // J + 1
            if n >= n_req:
                break
            n = n_req
        n = ((n + M_steps - 1) // M_steps) * M_steps
        m_bin = n // M_steps
        N_num = M_tri
        D_den = m_bin * J
        iv_0, iv_2, iv_4 = cls(0), cls(2), cls(4)
        pi_iv = (
            cls(vjd.Decimal("3.14159265358979323846264338"), vjd.Decimal("3.14159265358979323846264339"))
            if cls is vjd.DInterval
            else vjd.FInterval(math.pi)
        )
        delta_lo_iv = cls(D_lo + 4).sqrt() / iv_4
        delta_hi_iv = cls(D_hi + 4).sqrt() / iv_4
        brad_lo_iv = ((cls(n) * cls(D_lo).sqrt()) / (iv_2 * pi_iv)).sqrt()
        brad_hi_iv = ((cls(n) * cls(D_hi).sqrt()) / (iv_2 * pi_iv)).sqrt()
        rho_lo_iv = brad_lo_iv + delta_lo_iv
        rho_hi_iv = brad_hi_iv + delta_hi_iv
        sigma2_iv = iv_0
        for p in vjd.PRIMES:
            pk = p * p
            if pk > J - 1:
                break
            lp_iv = cls(p).ln()
            while pk <= J - 1:
                sigma2_iv = sigma2_iv + lp_iv / cls(pk)
                pk *= p
        slope_j_lo_iv = (cls(R) / rho_hi_iv).ln() - sigma2_iv
        Fw, dgap, Flb = solve_variational_fubini_jensen_iv(
            M_steps, N_num, D_den, K, rho_lo_iv, brad_lo_iv, delta_lo_iv,
            rho_hi_iv, brad_hi_iv, delta_hi_iv, n, R, J, slope_j_lo_iv, cls=cls, b0_frac=0.50
        )
        print(f"[{cls_name}] D=[3968539, 3970539]: F_w={float(Fw.lo):.9f}, dgap={float(dgap.hi):.3e}, F_lb={Flb.lo}")

    # 2. Scan infinite tail threshold with Fubini-Jensen C^1 functional:
    for D_test in [5760000, 5500000]:
        ok, gap_f, slope_f, gap_iv, det = certify_infinite_tail_fubini_jensen(D_test, cls=vjd.FInterval)
        print(f"[Tail FInterval] D_lo={D_test}: ok={ok}, gap={gap_f:+.9f}, F_lb={det['F_lb']:.6f}, dgap={det['duality_gap']:.2e}, save_deriv={det['save_deriv']:.6f}")
        assert ok and gap_f > 0
    for D_test in [5760000, 5500000]:
        ok, gap_f, slope_f, gap_iv, det = certify_infinite_tail_fubini_jensen(D_test, cls=vjd.DInterval)
        print(f"[Tail DInterval] D_lo={D_test}: ok={ok}, gap=[{gap_iv.lo}, {gap_iv.hi}], F_lb={det['F_lb']:.9f}, dgap={det['duality_gap']:.2e}, slope={slope_f:.6f}")
        assert ok and gap_iv.lo > 0

    # 3. Regression Test on 1D Fubini Unit-Slice Identity B_m(c) = sum_{i=1}^n (c_i - m)_+ = M_tri - n*m + sum_{i=1}^n (m - c_i)_+
    #    and Slice Slope Bound on \tilde{I}_m = [J - m - 1, J - m] (Referee Test Case: K=16, S=24, R=384, J=20, n=800, M_tri=4800):
    K_r, S_r, R_r, J_r, n_r, M_tri_r = 16, 24, 384, 20, 800, 4800
    for label_r, c_vec in [("uniform c_i=6", [6] * n_r), ("bimodal [2]^400+[10]^400", [2] * 400 + [10] * 400)]:
        assert sum(c_vec) == M_tri_r
        j_top_r = sorted([J_r - s for c_v in c_vec for s in range(1, c_v + 1)])
        assert len(j_top_r) == M_tri_r
        for sl_r in (1.0, 4.0):
            exp_neg_r = math.exp(-sl_r)
            tot_true_r = 0.0
            for k_idx in range(1, M_tri_r + 1):
                G_k = k_idx / float(M_tri_r)
                u_k = 1.0 - math.sqrt(1.0 - G_k)
                j_u_k = J_r - (M_tri_r - k_idx) / float(n_r)
                jt_k = j_top_r[k_idx - 1]
                if j_u_k > jt_k:
                    dx = (j_u_k - jt_k) / 40.0
                    for s_i in range(40):
                        xm = jt_k + (s_i + 0.5) * dx
                        if u_k > xm / float(R_r):
                            tot_true_r += dx * max(0.0, sl_r + math.log(u_k - xm / float(R_r)))
            tot_slice_r = 0.0
            for m_v in range(1, J_r):
                # On unit slice \tilde{I}_m = [J - m - 1, J - m], every x in \tilde{I}_m satisfies x <= J - m = R * c_hi_m:
                A_m = max(0, M_tri_r - n_r * m_v)
                B_m = M_tri_r - n_r * m_v + sum(max(0, m_v - c_v) for c_v in c_vec)
                B_m_direct = sum(1 for jt in j_top_r if jt <= J_r - m_v - 1)
                assert B_m == sum(max(0, c_v - m_v) for c_v in c_vec) == B_m_direct
                c_hi_m = (J_r - m_v) / float(R_r)
                for k_idx in range(A_m + 1, B_m + 1):
                    j_u_k = J_r - (M_tri_r - k_idx) / float(n_r)
                    assert j_top_r[k_idx - 1] <= J_r - m_v - 1 and j_u_k >= J_r - m_v
                    G_k = k_idx / float(M_tri_r)
                    u_k = 1.0 - math.sqrt(1.0 - G_k)
                    if u_k > c_hi_m:
                        tot_slice_r += max(0.0, sl_r + math.log(u_k - c_hi_m))
            w_s_r = sorted([c_v / float(J_r) for c_v in c_vec])
            pref_w_r = [0.0] * (n_r + 1)
            for i_w in range(n_r):
                pref_w_r[i_w + 1] = pref_w_r[i_w] + w_s_r[i_w]
            for L_b_test in (5, 10, 19):
                mk_r = [int(round(r_i * (J_r - 1) / float(L_b_test))) for r_i in range(L_b_test + 1)]
                tot_blk_r = 0.0
                for r_i in range(L_b_test):
                    m_lo_i, m_hi_i = mk_r[r_i] + 1, mk_r[r_i + 1]
                    if m_lo_i > m_hi_i:
                        continue
                    cnt_i = m_hi_i - m_lo_i + 1
                    t0_i, t1_i = (m_lo_i - 1) / float(J_r), m_hi_i / float(J_r)
                    dt_i = t1_i - t0_i
                    G0_i = 1.0 - (n_r * m_hi_i) / float(M_tri_r)
                    chi_i = (J_r - m_lo_i) / float(R_r)
                    idx0 = bisect.bisect_right(w_s_r, t0_i)
                    idx1 = bisect.bisect_left(w_s_r, t1_i)
                    sq_i = idx0 * (0.5 * (t0_i + t1_i)) - pref_w_r[idx0]
                    for i_w in range(idx0, idx1):
                        sq_i += ((t1_i - w_s_r[i_w]) ** 2) / (2.0 * dt_i)
                    Df_i = sq_i / (M_tri_r / float(J_r))
                    for m_v in range(m_lo_i, m_hi_i + 1):
                        B_m_v = M_tri_r - n_r * m_v + sum(max(0, m_v - c_v) for c_v in c_vec)
                        assert G0_i + Df_i <= B_m_v / float(M_tri_r) + 1e-12
                    umin_i = min(1.0, chi_i + exp_neg_r)
                    Gmin_i = 1.0 - (1.0 - umin_i) ** 2
                    Gst_i = max(G0_i, Gmin_i)
                    Gend_i = min(1.0, G0_i + Df_i)
                    if Gend_i > Gst_i:
                        zst = max(exp_neg_r, 1.0 - math.sqrt(max(0.0, 1.0 - Gst_i)) - chi_i)
                        zhi = max(zst, 1.0 - math.sqrt(max(0.0, 1.0 - Gend_i)) - chi_i)
                        anti = lambda z_v: 2.0 * (1.0 - chi_i) * z_v * (sl_r - 1.0 + math.log(z_v)) - (z_v * z_v) * (sl_r - 0.5 + math.log(z_v))
                        tot_blk_r += cnt_i * M_tri_r * max(0.0, anti(zhi) - anti(zst))
                assert tot_blk_r <= tot_slice_r + 1e-9 <= tot_true_r + 1e-9
    print("[Unit-Slice Fubini Regression] Verified B_m(c) = sum(c_i - m)_+ and tot_blk <= tot_slice <= tot_true on K=16, S=24, R=384, J=20, n=800!")
