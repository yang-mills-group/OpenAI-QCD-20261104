import YM.QCD.Sparks.Cavern

/-! # for use BOTH with gradient (curl extraction) and without (loop/book extraction) -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Sparks
open Function Filter Lattice Wilson Lat Kit Eyrie Quarry Rudder Stationary Push.Uniform Run
open YM.Further.PhysicalPeriodLimitF933 Macrame Exterior Flume Finset
open scoped Topology Matrix Matrix.Norms.L2Operator BigOperators Classical ContDiff
variable {S : SparkMesh} {n N: Side} {i j : ℕ} (s:SparkMesh) {F: s.Field} {m:ℕ→ℕ} {r C:ℝ}

lemma into (i j:ℕ)(h:i≤j): (s.vista i j h).cut 0=0:= map_zero (splitter _)
lemma passThrough {i j} (h:i≤j)(p:Cover): (s.vista i j h).cut (wrap (s.n j) p)=wrap (s.n i) p:=Macrame.branch ..
lemma certificate {K: ℕ} (H: Clan s F)(P:ℕ)(x:Fin K→ Cnr (s.n P))(k:ℕ)(he:P ≤ k)(W : Fin K→ Cnr (s.n k))(hW: surge (F k) W = surge (F k) (expandC (s.vista P k he)∘ x)) (y:Site (s.n P)):
    Run.cell (surge (F P) x) 0 y=∑' p:Tilt K, if wrap (s.n P) p.1=y then
      (∏ i,W i ((wrap (s.n k) (p.2 i).1),(p.2 i).2)) • (occ (n:=s.n P) 0 p.1 • design (F k) p) else 0:=by
  let Y:=s.vista P k he; obtain ⟨d,hp,D⟩:=H.order P k he
  have hg:= pinhead (H.way P|>.ready) (H.way k|>.ready) x D; rw [← hW] at hg
  rw [calibrated Y d hp hg _ (into s ..)]
  let n:=s.n k; let I:= up (k:=K) n; let X:=Finset.univ.image I
  let f (p:Tilt K):Bundle:= if wrap (s.n P) p.1=y then
      (∏ i,W i ((wrap (s.n k) (p.2 i).1),(p.2 i).2)) • (occ (n:=s.n P) 0 p.1 • design (F k) p) else 0
  rw [show (∑' p:Tilt K,f p)=∑ p∈X, f p from tsum_eq_sum (fun i hi=> ?_)] -- rw defeq
  · unfold X; rw [sum_image (safe n).injOn]; apply sum_congr rfl; intro i _; simp only [f,I, n,designer]
    have hp : wrap (s.n P) (Lattice.lift i.1)=Y.cut i.1:= by
      rw [← passThrough s he (lift i.1), wrap_lift]
    unfold up; simp only [hp,Function.comp_apply,Prod.map,wrap_lift,id]
  unfold f; split; swap; rfl
  rw [design,if_neg (show ¬ AtMap (s.n k) i from fun v=>hi (mem_image.mpr ⟨down n i, Finset.mem_univ _, v⟩))]; simp
lemma chargeNext (hm:StrictMono m)(x:Cover) : ∀ᶠ j in atTop,Lattice.lift (wrap (s.n (m j)) x) = x := by
  have hh : ∀ i : Axis, ∀ᶠ p in atTop, -((s.n (m p)).val:ℤ)< 2*x i ∧ 2*x i ≤ ((s.n (m p)).val:ℤ):=by
    intro i; filter_upwards [(s.cofinal.comp hm.tendsto_atTop).eventually (eventually_gt_atTop (2*(x i).natAbs))] with p hp; change _ < (s.n (m p)).val at hp; omega
  exact (eventually_all.mpr hh).mono fun i H=>lift_eq_iff.mpr ⟨rfl,H⟩
lemma beam_use (k:ℕ){r : ℝ}(hr:0<r) : Summable (fun p:Tilt k=> (1+(timbre p:ℝ))^k*aim r p):= by
  let M := r/2
  have he := half_pos hr
  apply ((aim_supply k he).mul_left (YM.Extra.Iteration.momentPrice k M)).of_nonneg_of_le (fun i=> mul_nonneg (by positivity) (aim_pos ..).le)
  intro x
  have hp:= mul_le_mul_of_nonneg_right (YM.Extra.Iteration.spendMoment k he (show 0 ≤ (timbre x:ℝ) by positivity)) (aim_pos r x).le; apply hp.trans_eq
  unfold M aim; rw [mul_assoc, ← Real.exp_add]; congr 2; ring
-- use evaluation along any admissible volume cut, allows saturation n-offset
lemma directed (i:ℕ){k:ℕ}(x: Fin k→ Cnr (s.n i))(h:Clan s F) {K: Typewriter k} (he : Exhibit s F k r C m K)(hc: 0 ≤ C)(hr : 0<r) (y:Site (s.n i))
    (u : ∀ z:ℕ, Fin k→Cnr (s.n (m z)))(v: Nub→Fin k→ℝ)(b:ℝ)(hb:0≤b)
    (hy : ∀ (p:ℕ) (H:i ≤ m p), surge (F (m p)) (u p)=surge (F (m p)) (expandC (s.vista i (m p) H) ∘ x))
    (ht: ∀ w : Nub,∀ j: Fin k,Tendsto (fun p=>u p j (wrap (s.n (m p)) w.1,w.2)) atTop (𝓝 (v w j)))
    (hg: ∀ᶠ p in atTop,∀ w:Nub,∀ j : Fin k, |u p j ((wrap (s.n (m p)) w.1),w.2)| ≤ b*(1+ Laurent.size w.1)) :
      Run.cell (surge (F i) x) 0 y=∑' p:Tilt k, if wrap (s.n i) p.1=y then (∏ j,v (p.2 j) j) • (occ (n:=s.n i) 0 p.1 • K p) else 0:=by
  let X q (p:Tilt k):Bundle:= if wrap (s.n i) p.1=y then (∏ j,u q j (wrap (s.n (m q)) (p.2 j).1,(p.2 j).2)) • (occ (n:=s.n i) 0 p.1 • design (F (m q)) p) else 0
  have hX: ∀ᶠ q in atTop, Run.cell (surge (F i) x) 0 y=∑' p,X q p:= (he.climbs.tendsto_atTop.eventually_ge_atTop i).mono fun q hQ=> certificate s h i x _ hQ (u q) (hy q hQ) y
  have hV : Tendsto (fun q=>∑' p,X q p) atTop (𝓝 (Run.cell (surge (F i) x) 0 y)):=tendsto_const_nhds.congr' hX
  refine tendsto_nhds_unique hV (tendsto_tsum_of_dominated_convergence ((beam_use k hr).mul_left (b^k*C)) ?_ ?_)
  · intro p; unfold X; split; swap; exact tendsto_const_nhds
    refine Tendsto.smul ?_ ((he.shape p).const_smul _)
    apply tendsto_finsetProd _; intro i _; exact ht ..
  filter_upwards [hg] with q hh
  intro p; unfold X; split
  next hi=>
    rw [norm_smul,norm_smul,pathLength,one_mul,norm_prod]; let W (j:Fin k):ℝ:=‖u q j (wrap (s.n (m q)) (p.2 j).1,(p.2 j).2)‖
    have hh j: W j≤b*(1+timbre p):=(hh _ j).trans (by gcongr; unfold timbre; exact le_trans (single_le_sum (fun j _=> Nat.zero_le (Laurent.size (p.2 j).1)) (Finset.mem_univ _)) (Nat.le_add_left ..))
    apply (mul_le_mul (prod_le_prod (s:=Finset.univ) (fun i _=> show 0 ≤ W i from norm_nonneg _) (fun i _=> hh i)) (he.price (m q) _) (norm_nonneg _) (prod_nonneg (fun _ _=> mul_nonneg hb (by positivity)))).trans_eq; rw [prod_const,card_univ,Fintype.card_fin, mul_pow]; ring
  rw [norm_zero]; have := aim_pos r p; positivity
end YM.QCD.Sparks
