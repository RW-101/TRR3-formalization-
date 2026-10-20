import inspect
import subprocess
import sys
import time
import numpy as np
import matplotlib as mpl
import matplotlib.pyplot as plt
from scipy.signal import butter, filtfilt, hilbert
from scipy.stats import mannwhitneyu, wilcoxon

try:
    import mne
except ImportError:
    subprocess.check_call([sys.executable, "-m", "pip", "install", "-q", "mne"])
    import mne
from mne.datasets import eegbci

mne.set_log_level("ERROR")
mpl.rcParams["pdf.fonttype"] = 42
mpl.rcParams["ps.fonttype"] = 42

CANONICAL_20 = [
    "Fp1", "Fp2", "F7", "F3", "Fz", "F4", "F8", "T7", "C3", "Cz",
    "C4", "T8", "P7", "P3", "Pz", "P4", "P8", "O1", "Oz", "O2",
]
POST_CHANNELS = ["P7", "P3", "Pz", "P4", "P8", "O1", "Oz", "O2"]
ANT_CHANNELS = ["Fp1", "Fp2", "F7", "F3", "Fz", "F4", "F8", "T7", "C3", "Cz", "C4", "T8"]

MIRRORS = [
    "https://physionet-open.s3.amazonaws.com/eegmmidb/1.0.0/",
    "https://physionet.org/files/eegmmidb/1.0.0/",
]


def fetch_eeg_safe(s_id, runs=(1, 2)):
    sig = inspect.signature(eegbci.load_data)
    kw = {"subjects": s_id} if "subjects" in sig.parameters else {"subject": s_id}
    for url in MIRRORS:
        for attempt in range(3):
            try:
                return eegbci.load_data(
                    runs=list(runs), update_path=True, base_url=url, verbose=False, **kw
                )
            except Exception:
                time.sleep(1.5 * (attempt + 1))
    raise RuntimeError(f"Failed to download subject {s_id}.")


def compute_f2_persistence(D, tol=1e-12):
    """Exact F_2 Vietoris-Rips boundary reduction returning (L_tot(H0), L_max(H1), L_tot(H1))."""
    n, md = D.shape[0], float(np.max(D))
    ed = sorted((float(D[u, v]), (u, v)) for u in range(n) for v in range(u + 1, n))
    ei = {e[1]: i for i, e in enumerate(ed)}
    tr = sorted(
        (max(float(D[u, v]), float(D[v, w]), float(D[u, w])), (u, v, w))
        for u in range(n) for v in range(u + 1, n) for w in range(v + 1, n)
    )

    def red(cols):
        p2c, rc, piv = {}, [], []
        for j, m in enumerate(cols):
            while m and (m.bit_length() - 1) in p2c:
                m ^= rc[p2c[m.bit_length() - 1]]
            rc.append(m)
            p = (m.bit_length() - 1) if m else -1
            if m:
                p2c[p] = j
            piv.append(p)
        return piv, p2c

    p1, m1 = red([(1 << u) | (1 << v) for _, (u, v) in ed])
    _, m2 = red(
        [(1 << ei[(u, v)]) | (1 << ei[(v, w)]) | (1 << ei[(u, w)]) for _, (u, v, w) in tr]
    )
    l_h0 = sum(ed[m1[v]][0] for v in m1 if ed[m1[v]][0] > tol)
    h1_bars = [
        max(0.0, (tr[m2[i]][0] if i in m2 else md) - ed[i][0])
        for i, p in enumerate(p1) if p == -1
    ]
    return float(l_h0), float(max(h1_bars, default=0.0)), float(sum(b for b in h1_bars if b > tol))


def compute_rectified_lag_imcoh(ep_band, sfreq, sub_sec=1.0, step_sec=0.5, gamma=0.85):
    """Sub-window Rectified & Lag-Orthogonalized Imaginary Coherency (rLagImCoh)."""
    n_ch, n_samp = ep_band.shape
    sub_len = int(sub_sec * sfreq)
    step_len = int(step_sec * sfreq)
    win = np.hanning(sub_len)[None, :]
    z_full = hilbert(ep_band, axis=-1)

    acc = np.zeros((n_ch, n_ch), dtype=np.float64)
    count = 0
    for st in range(0, n_samp - sub_len + 1, step_len):
        z_seg = z_full[:, st : st + sub_len] * win
        s_uv = (z_seg @ z_seg.conj().T) / sub_len
        p_u = np.real(np.diag(s_uv))
        re_sq = np.real(s_uv) ** 2
        im_abs = np.abs(np.imag(s_uv))
        denom = np.sqrt(np.maximum(1e-15, np.outer(p_u, p_u) - gamma * re_sq))
        acc += np.clip(im_abs / denom, 0.0, 1.0)
        count += 1

    ic = acc / max(1, count)
    np.fill_diagonal(ic, 1.0)
    D = np.maximum(0.0, 1.0 - ic)
    np.fill_diagonal(D, 0.0)
    return D


def eval_stats(eo, ec, polarity=None):
    eo, ec = np.asarray(eo, float), np.asarray(ec, float)
    n1, n2 = len(eo), len(ec)
    vp = ((n1 - 1) * np.var(eo, ddof=1) + (n2 - 1) * np.var(ec, ddof=1)) / (n1 + n2 - 2)
    d = float((np.mean(ec) - np.mean(eo)) / (np.sqrt(vp) + 1e-15))
    _, p = mannwhitneyu(ec, eo, alternative="two-sided")
    y = np.r_[np.zeros(n1), np.ones(n2)]
    sign = polarity if polarity is not None else (-1.0 if d < 0 else 1.0)
    s = np.r_[eo, ec] * sign
    idx = np.argsort(s)[::-1]
    tpr = np.r_[0.0, np.cumsum(y[idx]) / n2, 1.0]
    fpr = np.r_[0.0, np.cumsum(1.0 - y[idx]) / n1, 1.0]
    auc = float(np.trapezoid(tpr, fpr) if hasattr(np, "trapezoid") else np.trapz(tpr, fpr))
    return d, float(p), auc, fpr, tpr


def subject_level_metrics(eo_list, ec_list, polarity=1.0):
    diffs, subj_aucs = [], []
    for eo, ec in zip(eo_list, ec_list):
        diffs.append(polarity * (float(np.mean(ec)) - float(np.mean(eo))))
        _, _, auc_s, _, _ = eval_stats(eo, ec, polarity=polarity)
        subj_aucs.append(auc_s)
    _, p_w = wilcoxon(diffs, alternative="two-sided")
    n_pos = sum(1 for x in diffs if x > 0)
    return (
        float(p_w),
        n_pos,
        len(diffs),
        float(np.mean(subj_aucs)),
        float(np.std(subj_aucs, ddof=1) / np.sqrt(len(subj_aucs))),
    )


def calibrate_single_window(X_eo, X_ec, mu_p, var_p, k, tau0=3.0, nu0=5.0):
    """Strictly causal single-window Empirical Bayes NIG calibration on prefix X_eo[0:k]."""
    ke = min(max(0, int(k)), len(X_eo))
    if ke == 0:
        mu_post, var_post = mu_p, var_p
    else:
        sl = X_eo[:ke]
        mu_h = np.mean(sl, axis=0)
        s2_h = np.var(sl, axis=0, ddof=1) if ke >= 2 else np.zeros_like(mu_p)
        df = max(0, ke - 1)
        mu_post = (ke * mu_h + tau0 * mu_p) / (ke + tau0)
        var_post = (
            df * s2_h + nu0 * var_p + (ke * tau0 / (ke + tau0)) * ((mu_h - mu_p) ** 2)
        ) / (df + nu0)
    sd_post = np.sqrt(var_post) + 1e-12
    return (X_eo - mu_post) / sd_post, (X_ec - mu_post) / sd_post


def fit_lda_direction(Z_eo, Z_ec, reg_lda=0.20):
    """Fit scale-normalized Regularized Fisher Discriminant direction on training fold."""
    if Z_eo.shape[1] == 1:
        w = np.array([1.0 if np.mean(Z_ec) >= np.mean(Z_eo) else -1.0])
    else:
        m0 = np.mean(Z_eo, axis=0)
        m1 = np.mean(Z_ec, axis=0)
        cov_pool = 0.5 * (np.cov(Z_eo, rowvar=False) + np.cov(Z_ec, rowvar=False))
        diag_var = np.maximum(1e-12, np.diag(cov_pool))
        cov_reg = (1.0 - reg_lda) * cov_pool + reg_lda * np.diag(diag_var)
        w = np.linalg.solve(cov_reg, m1 - m0)
    proj_std = float(np.std(Z_eo @ w, ddof=1)) + 1e-12
    return w / proj_std


def two_stage_stein_loso(inv_dict, cal_dict, k, k_pool=10, tau0=3.0, nu0=5.0, reg_lda=0.20):
    """Post-Inversion Empirical Bayes Stein Shrinkage Fusion under strict LOSO-CV."""
    subjs = sorted(cal_dict.keys())
    eo_full, ec_full, eo_hold, ec_hold = [], [], [], []
    eo_subj_list, ec_subj_list = [], []
    alpha_k = float(k) / float(k + tau0)

    for s in subjs:
        tr_subjs = [j for j in subjs if j != s]

        I_tr_eo = np.vstack([inv_dict[j][1] for j in tr_subjs])
        I_tr_ec = np.vstack([inv_dict[j][2] for j in tr_subjs])
        mu_i = np.mean(I_tr_eo, axis=0)
        sd_i = np.std(I_tr_eo, axis=0, ddof=1) + 1e-12
        ZI_tr_eo = (I_tr_eo - mu_i) / sd_i
        ZI_tr_ec = (I_tr_ec - mu_i) / sd_i
        w_inv = fit_lda_direction(ZI_tr_eo, ZI_tr_ec, reg_lda=reg_lda)

        u_inv_eo = ((inv_dict[s][1] - mu_i) / sd_i) @ w_inv
        u_inv_ec = ((inv_dict[s][2] - mu_i) / sd_i) @ w_inv

        if k == 0:
            proj_eo, proj_ec = u_inv_eo, u_inv_ec
        else:
            X_tr_raw_eo = np.vstack([cal_dict[j][1] for j in tr_subjs])
            mu_p = np.mean(X_tr_raw_eo, axis=0)
            var_p = np.var(X_tr_raw_eo, axis=0, ddof=1) + 1e-12

            Z_tr_eo_l, Z_tr_ec_l = [], []
            for j in tr_subjs:
                zj_eo, zj_ec = calibrate_single_window(
                    cal_dict[j][1], cal_dict[j][2], mu_p, var_p, k=k, tau0=tau0, nu0=nu0
                )
                Z_tr_eo_l.append(zj_eo)
                Z_tr_ec_l.append(zj_ec)
            Z_tr_eo = np.vstack(Z_tr_eo_l)
            Z_tr_ec = np.vstack(Z_tr_ec_l)
            w_cal = fit_lda_direction(Z_tr_eo, Z_tr_ec, reg_lda=reg_lda)

            Z_s_eo, Z_s_ec = calibrate_single_window(
                cal_dict[s][1], cal_dict[s][2], mu_p, var_p, k=k, tau0=tau0, nu0=nu0
            )
            u_cal_eo = Z_s_eo @ w_cal
            u_cal_ec = Z_s_ec @ w_cal

            proj_eo = (1.0 - alpha_k) * u_inv_eo + alpha_k * u_cal_eo
            proj_ec = (1.0 - alpha_k) * u_inv_ec + alpha_k * u_cal_ec

        eo_full.append(proj_eo)
        ec_full.append(proj_ec)
        eo_subj_list.append(proj_eo)
        ec_subj_list.append(proj_ec)
        if k <= k_pool:
            eo_hold.append(proj_eo[k_pool:])
            ec_hold.append(proj_ec[k_pool:])

    return (
        np.concatenate(eo_full),
        np.concatenate(ec_full),
        np.concatenate(eo_hold) if eo_hold else np.array([]),
        np.concatenate(ec_hold) if ec_hold else np.array([]),
        eo_subj_list,
        ec_subj_list,
    )


def run_stage7_flawless():
    all_ids = list(range(1, 21))
    post_idx = [CANONICAL_20.index(c) for c in POST_CHANNELS]
    ant_idx = [CANONICAL_20.index(c) for c in ANT_CHANNELS]

    old_h0 = {s: {} for s in all_ids}
    post_h0 = {s: {} for s in all_ids}
    grad_h0 = {s: {} for s in all_ids}
    pure_inv = {s: {} for s in all_ids}
    pure_cal = {s: {} for s in all_ids}
    hyb_inv = {s: {} for s in all_ids}
    hyb_cal = {s: {} for s in all_ids}

    print("Running Stage 7 Final Corrected Audit (Post-Inversion Stein Fusion, N=20, 1160 epochs)...")
    for s_id in all_ids:
        paths = fetch_eeg_safe(s_id, runs=(1, 2))
        for r_id, p in zip([1, 2], paths):
            raw = mne.io.read_raw_edf(p, preload=True, verbose=False)
            eegbci.standardize(raw)
            raw.pick([c for c in CANONICAL_20 if c in raw.ch_names])
            raw.set_eeg_reference("average", projection=False, verbose=False)
            raw.filter(1.0, 45.0, verbose=False)
            sf = float(raw.info["sfreq"])
            dt = raw.get_data()
            ws, hs = int(4 * sf), int(2 * sf)

            b_a, a_a = butter(4, [8.0 / (0.5 * sf), 13.0 / (0.5 * sf)], btype="band")
            b_a1, a_a1 = butter(4, [7.5 / (0.5 * sf), 10.5 / (0.5 * sf)], btype="band")
            b_a2, a_a2 = butter(4, [10.0 / (0.5 * sf), 13.5 / (0.5 * sf)], btype="band")
            b_b, a_b = butter(4, [14.0 / (0.5 * sf), 26.0 / (0.5 * sf)], btype="band")
            b_t, a_t = butter(4, [4.0 / (0.5 * sf), 7.5 / (0.5 * sf)], btype="band")

            l_old, l_post, l_grad, l_p_inv, l_p_cal, l_h_inv, l_h_cal = [], [], [], [], [], [], []
            for st in range(0, dt.shape[1] - ws + 1, hs):
                ep = dt[:, st : st + ws]
                ep_a = filtfilt(b_a, a_a, ep, axis=-1)
                ep_a1 = filtfilt(b_a1, a_a1, ep, axis=-1)
                ep_a2 = filtfilt(b_a2, a_a2, ep, axis=-1)
                ep_b = filtfilt(b_b, a_b, ep, axis=-1)
                ep_t = filtfilt(b_t, a_t, ep, axis=-1)

                z = hilbert(ep_a, axis=-1)
                pw = np.mean(np.abs(z) ** 2, -1)
                ic_old = np.clip(
                    np.abs(np.imag(z @ z.conj().T / ws)) / (np.sqrt(np.outer(pw, pw)) + 1e-15),
                    0.0,
                    1.0,
                )
                D_old = np.maximum(0.0, 1.0 - ic_old)
                np.fill_diagonal(D_old, 0.0)
                h0_glob_old, _, _ = compute_f2_persistence(D_old)
                l_old.append(h0_glob_old)

                D_rlag_a = compute_rectified_lag_imcoh(ep_a, sf, 1.0, 0.5, 0.85)
                D_post_a = D_rlag_a[np.ix_(post_idx, post_idx)]
                D_ant_a = D_rlag_a[np.ix_(ant_idx, ant_idx)]
                h0_post_a, h1_post_a, h1_tot_post_a = compute_f2_persistence(D_post_a)
                h0_ant_a, _, _ = compute_f2_persistence(D_ant_a)

                D_post_a1 = compute_rectified_lag_imcoh(ep_a1[post_idx], sf, 1.0, 0.5, 0.85)
                D_post_a2 = compute_rectified_lag_imcoh(ep_a2[post_idx], sf, 1.0, 0.5, 0.85)
                D_post_b = compute_rectified_lag_imcoh(ep_b[post_idx], sf, 1.0, 0.5, 0.85)
                h0_p_a1, _, _ = compute_f2_persistence(D_post_a1)
                h0_p_a2, _, _ = compute_f2_persistence(D_post_a2)
                h0_p_b, _, _ = compute_f2_persistence(D_post_b)

                mean_edge_post = h0_post_a / 7.0
                mean_edge_ant = h0_ant_a / 11.0
                grad_val = mean_edge_post - mean_edge_ant
                grad_a1 = h0_p_a1 / 7.0 - mean_edge_ant
                grad_a2 = h0_p_a2 / 7.0 - mean_edge_ant
                cross_ab = mean_edge_post - h0_p_b / 7.0

                pwr_post_a = np.mean(ep_a[post_idx] ** 2)
                pwr_ant_a = np.mean(ep_a[ant_idx] ** 2)
                pwr_post_b = np.mean(ep_b[post_idx] ** 2)
                pwr_post_t = np.mean(ep_t[post_idx] ** 2)
                rel_post_alpha = np.log((pwr_post_a + 1e-15) / (pwr_post_b + pwr_post_t + 1e-15))
                ant_post_ratio = np.log((pwr_post_a + 1e-15) / (pwr_ant_a + 1e-15))
                spec_topo_val = mean_edge_post * np.exp(-0.5 * rel_post_alpha)

                l_post.append(mean_edge_post)
                l_grad.append(grad_val)
                l_p_inv.append([grad_val])
                l_p_cal.append(
                    [grad_val, grad_a1, grad_a2, cross_ab, mean_edge_post, h1_post_a, h1_tot_post_a]
                )
                l_h_inv.append([grad_val, rel_post_alpha, ant_post_ratio, spec_topo_val])
                l_h_cal.append(
                    [
                        grad_val,
                        grad_a1,
                        grad_a2,
                        cross_ab,
                        mean_edge_post,
                        h1_post_a,
                        h1_tot_post_a,
                        rel_post_alpha,
                        ant_post_ratio,
                        spec_topo_val,
                    ]
                )

            old_h0[s_id][r_id] = np.array(l_old, float)
            post_h0[s_id][r_id] = np.array(l_post, float)
            grad_h0[s_id][r_id] = np.array(l_grad, float)
            pure_inv[s_id][r_id] = np.array(l_p_inv, float)
            pure_cal[s_id][r_id] = np.array(l_p_cal, float)
            hyb_inv[s_id][r_id] = np.array(l_h_inv, float)
            hyb_cal[s_id][r_id] = np.array(l_h_cal, float)

    print("=" * 126)
    print("PART 1: ZERO-SHOT ABLATION (k=0, 0 s, N=20, 1160 EPOCHS) — BALANCED HOLDOUT (EO[10:] vs EC[10:])")
    print("=" * 126)
    print(f"{'Zero-Shot Architecture (k=0, 0 s)':<44} | {'Cohen d':>7} | {'Full AUC':>8} | {'Holdout AUC':>11} | {'Mean Subj AUC':>15} | {'Subj Wilcoxon p'}")
    print("-" * 126)

    for nm, dct, pol in [
        ("1. Stage 6 Global H_0 (Baseline ImCoh)", old_h0, -1.0),
        ("2. Pure Topo: Posterior rLagImCoh H_0", post_h0, -1.0),
        ("3. Pure Topo: Spatial Gradient (Post-Ant) H_0", grad_h0, -1.0),
    ]:
        e_l = [dct[s][1] for s in all_ids]
        c_l = [dct[s][2] for s in all_ids]
        e_a, c_a = np.concatenate(e_l), np.concatenate(c_l)
        e_h = np.concatenate([dct[s][1][10:] for s in all_ids])
        c_h = np.concatenate([dct[s][2][10:] for s in all_ids])
        d, _, af, _, _ = eval_stats(e_a, c_a, polarity=pol)
        _, _, ah, _, _ = eval_stats(e_h, c_h, polarity=pol)
        p_w, n_pos, n_tot, m_sauc, se_sauc = subject_level_metrics(e_l, c_l, polarity=pol)
        print(f"{nm:<44} | {d:>+7.2f} | {af:>8.3f} | {ah:>11.3f} | {f'{m_sauc:.3f} +/- {se_sauc:.3f}':>15} | {p_w:.2e} ({n_pos}/{n_tot})")

    print("\n" + "=" * 126)
    print("PART 2: POST-INVERSION STEIN SHRINKAGE FUSION (ZERO-SHOT ANCHOR + CAUSAL BAYES CALIBRATION, N=20 LOSO-CV)")
    print("=" * 126)
    print(f"{'Model & Strictly Causal Budget k (N=20)':<44} | {'Time':<5} | {'Cohen d':>7} | {'Full AUC':>8} | {'Holdout AUC':>11} | {'Mean Subj AUC':>15} | {'Subj Wilcoxon p'}")
    print("-" * 126)

    k_grid = [0, 1, 2, 3, 5, 10, 29]
    auc_pure_full, auc_pure_hold = [], []
    auc_hyb_full, auc_hyb_hold = [], []

    for k in k_grid:
        sec = 0 if k == 0 else (4 + (k - 1) * 2)
        eo_p, ec_p, eoh_p, ech_p, sl_eo_p, sl_ec_p = two_stage_stein_loso(
            pure_inv, pure_cal, k, k_pool=10, tau0=3.0, nu0=5.0
        )
        d_p, _, af_p, _, _ = eval_stats(eo_p, ec_p, polarity=+1.0)
        ah_p = eval_stats(eoh_p, ech_p, polarity=+1.0)[2] if len(eoh_p) > 0 else np.nan
        pw_p, npos_p, ntot_p, ms_p, ses_p = subject_level_metrics(sl_eo_p, sl_ec_p, polarity=+1.0)
        auc_pure_full.append(af_p)
        auc_pure_hold.append(ah_p if not np.isnan(ah_p) else af_p)
        h_sp = f"{ah_p:.3f}" if not np.isnan(ah_p) else "N/A (Full)"
        print(f"{f'Pure Topological TRR (F_2 only, k={k})':<44} | {f'{sec}s':<5} | {d_p:>+7.2f} | {af_p:>8.3f} | {h_sp:>11} | {f'{ms_p:.3f} +/- {ses_p:.3f}':>15} | {pw_p:.2e} ({npos_p}/{ntot_p})")

    print("-" * 126)
    for k in k_grid:
        sec = 0 if k == 0 else (4 + (k - 1) * 2)
        eo_h, ec_h, eoh_h, ech_h, sl_eo_h, sl_ec_h = two_stage_stein_loso(
            hyb_inv, hyb_cal, k, k_pool=10, tau0=3.0, nu0=5.0
        )
        d_h, _, af_h, _, _ = eval_stats(eo_h, ec_h, polarity=+1.0)
        ah_h = eval_stats(eoh_h, ech_h, polarity=+1.0)[2] if len(eoh_h) > 0 else np.nan
        pw_h, npos_h, ntot_h, ms_h, ses_h = subject_level_metrics(sl_eo_h, sl_ec_h, polarity=+1.0)
        auc_hyb_full.append(af_h)
        auc_hyb_hold.append(ah_h if not np.isnan(ah_h) else af_h)
        h_sh = f"{ah_h:.3f}" if not np.isnan(ah_h) else "N/A (Full)"
        print(f"{f'Hybrid SpecTopo TRR (Topo + Power, k={k})':<44} | {f'{sec}s':<5} | {d_h:>+7.2f} | {af_h:>8.3f} | {h_sh:>11} | {f'{ms_h:.3f} +/- {ses_h:.3f}':>15} | {pw_h:.2e} ({npos_h}/{ntot_h})")
    print("=" * 126)

    fig, (ax0, ax1) = plt.subplots(1, 2, figsize=(11.4, 4.6), dpi=150)
    fig.subplots_adjust(left=0.07, right=0.98, bottom=0.17, top=0.86, wspace=0.24)

    eo_o0 = np.concatenate([old_h0[s][1] for s in all_ids])
    ec_o0 = np.concatenate([old_h0[s][2] for s in all_ids])
    _, _, auc_o0, fpr_o0, tpr_o0 = eval_stats(eo_o0, ec_o0, polarity=-1.0)
    ax0.plot(fpr_o0, tpr_o0, "--", lw=1.6, color="gray", label=f"Stage 6 Global $H_0$ ($k=0$, AUC={auc_o0:.3f})")

    eo_g0 = np.concatenate([grad_h0[s][1] for s in all_ids])
    ec_g0 = np.concatenate([grad_h0[s][2] for s in all_ids])
    _, _, auc_g0, fpr_g0, tpr_g0 = eval_stats(eo_g0, ec_g0, polarity=-1.0)
    ax0.plot(fpr_g0, tpr_g0, "-.", lw=1.9, color="#1f77b4", label=f"Pure Topo Spatial Gradient $H_0$ ($k=0$, AUC={auc_g0:.3f})")

    eo_p3, ec_p3, _, _, _, _ = two_stage_stein_loso(pure_inv, pure_cal, 3, k_pool=10, tau0=3.0, nu0=5.0)
    _, _, auc_p3, fpr_p3, tpr_p3 = eval_stats(eo_p3, ec_p3, polarity=+1.0)
    ax0.plot(fpr_p3, tpr_p3, "-", lw=2.1, color="#9467bd", label=f"Pure Topological TRR ($k=3$, 8 s, AUC={auc_p3:.3f})")

    eo_h3, ec_h3, _, _, _, _ = two_stage_stein_loso(hyb_inv, hyb_cal, 3, k_pool=10, tau0=3.0, nu0=5.0)
    _, _, auc_h3, fpr_h3, tpr_h3 = eval_stats(eo_h3, ec_h3, polarity=+1.0)
    ax0.plot(fpr_h3, tpr_h3, "-", lw=2.2, color="#d62728", label=f"Hybrid SpecTopo TRR ($k=3$, 8 s, AUC={auc_h3:.3f})")

    ax0.plot([0, 1], [0, 1], "k:", lw=0.8)
    ax0.set_title("A. Pure Topology vs. Hybrid SpecTopo ROC (N=20)", fontsize=10, fontweight="bold", pad=8)
    ax0.set_xlabel("False Positive Rate (FPR)", fontsize=9.5)
    ax0.set_ylabel("True Positive Rate (TPR)", fontsize=9.5)
    ax0.grid(True, alpha=0.3)
    ax0.legend(loc="lower right", fontsize=7.5)

    x_idx = range(len(k_grid))
    x_lbl = [f"k={k}\n({0 if k==0 else 4+(k-1)*2}s)" for k in k_grid]
    ax1.plot(x_idx, auc_hyb_full, "o-", lw=2.1, color="#d62728", label="Hybrid SpecTopo TRR (All 1160 epochs)")
    ax1.plot(range(len(k_grid) - 1), auc_hyb_hold[:-1], "s--", lw=1.6, color="#ff7f0e", label="Hybrid SpecTopo TRR (Holdout EO[10:] vs EC[10:])")
    ax1.plot(x_idx, auc_pure_full, "^-", lw=2.1, color="#9467bd", label="Pure Topological TRR (All 1160 epochs, 0% Power)")
    ax1.plot(range(len(k_grid) - 1), auc_pure_hold[:-1], "d:", lw=1.6, color="#1f77b4", label="Pure Topological TRR (Holdout EO[10:] vs EC[10:])")
    ax1.axhline(auc_g0, color="#2ca02c", ls="-.", lw=1.3, label=f"Zero-Shot Pure Spatial Gradient $H_0$ ({auc_g0:.3f})")
    ax1.set_xticks(list(x_idx))
    ax1.set_xticklabels(x_lbl, fontsize=8)
    ax1.set_title("B. Post-Inversion Stein Calibration Scaling (LOSO-CV)", fontsize=10, fontweight="bold", pad=8)
    ax1.set_xlabel("Strictly Causal Calibration Budget k (Resting-State EO Prefix)", fontsize=9.5)
    ax1.set_ylabel("Classification Accuracy (ROC-AUC)", fontsize=9.5)
    ax1.set_ylim(0.74, 0.97)
    ax1.grid(True, alpha=0.3)
    ax1.legend(loc="lower right", fontsize=7.2, framealpha=0.92)

    fig.savefig("trr_stage7_flawless_N20.pdf", format="pdf", bbox_inches="tight", pad_inches=0.18)
    try:
        from google.colab import files
        files.download("trr_stage7_flawless_N20.pdf")
    except Exception:
        pass
    plt.show()


if __name__ == "__main__":
    run_stage7_flawless()
