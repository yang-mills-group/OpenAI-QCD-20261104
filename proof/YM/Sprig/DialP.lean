import YM.Sprig.Video
import YM.Sprig.Scribe
/-! Transfer quiescent basis comparison to all spacetime jets. -/
set_option autoImplicit false
noncomputable section
namespace YM.Intag.Sprig
open Function Filter MeasureTheory RG Lattice Wilson Cells
open Massive Massive.Patria Massive.Patria.Hub Massive.Patria.Depth Massive.Patria.Rolls QCD QCD.Tide Tarot QCD.Lat QCD.Grass Massive.Patria.Exposure Massive.Lyre Massive.Lyre.Goblet Massive.Romance
open scoped BigOperators ContDiff Topology Classical TensorProduct Matrix.Norms.L2Operator ComplexOrder Interval
variable {C:Sequence} {D d d' n:ℕ} (P:Calibration C)
open YM.Eden Tarot.Vista CardsT QCD.Acre.Stratum.MarchQ QCD.Acre.Stratum.MarchQ.Suburb QCD.Acre.Stratum.MarchQ.Suburb.Talis QCD.Acre.Stratum.MarchQ.Suburb.Talis.Grammar Sapphire MintV
open Poised Display Plans Sieve Plans.Stamp SourceRead Canvas Ibis QCD.Plum Massive.Elm.SparK.Arbor.Gallery
open UV Vale Massive.Needle Massive.Tarn Massive.Fir YM.Fir.NoteF Massive.Elm.SparK.Arbor.PlaneG
variable (φ:ℕ→ℕ)(Q:Massive.Tarn.Choir)(hQ:Q.Harmony P φ)
open Function Set Finset Metric Compass
namespace Canopy
variable {P φ Q}(E:Canopy P φ Q)(S:KForm Q)
variable (x: Fin n→ Texts) (hx:∀ i,Loaded E (x i)) (s:Groom Q S)(H:Money E S)
noncomputable abbrev expectP (x:Fin n→Texts)(y:Points n):= UV.Free.wick (fun j=>(x j).1) y (fun j=>(x j).2.mark)
noncomputable def errorP (i:ℕ):Points n→ℂ:= (E.risingH S x i)-expectP x
-- should discharge per unmarked phase. room.S Cost.A.Mesh.
structure Troupe :Prop where
     awake (n:ℕ)(x:Fin n→Texts)(hx:∀ i,Loaded E (x i))(K:Set (Points n))(hk:IsCompact K)(h:K⊆conf n)(q:ℕ)(ε:ℝ)(hz:0<ε):∀ᶠ i in atTop, let A:=E.B i; ∀ (f: Fin n→ Cover), let y:=points (A.qR A.ℓ ∘ f); y∈K→ E.cc i^q * ‖E.errorP S x i y‖ ≤ ε
local instance choir_n (n:ℕ):ContinuousSMul ℝ (Points n):= inferInstance
set_option maxHeartbeats 510000
lemma scented(j:ℕ)(y:Points n)(hc:y∈conf n):ContDiffAt ℝ (j:ℕ) (expectP x) y:= (UV.Free.Sip.smoothC hc (fun j=>(x j).1) (fun j=> (x j).2.mark.val)).of_le le_top
include hQ H s hx
-- Poly.S compute for all jets.
local notation "δ" i:arg=> E.cc i
lemma period(i j:ℕ)(y:Points n)(hc:y∈conf n):ContDiffAt ℝ (j:ℕ) (E.errorP S x i) y:= (livingZ hQ E S x s _ _ _ hc).sub (scented x j y hc)
lemma errs (j:ℕ)(K:Set (Points n))(hk:IsCompact K)(hs:K⊆conf n):∃ m:ℕ,∃ C:ℝ,0 ≤ C ∧∀ᶠ i in atTop,∀ y∈K, ‖iteratedFDeriv ℝ j (E.errorP S x i) y‖≤ C * E.cc i^m:=by
     obtain ⟨m,A,hA,hv⟩:= pricing hQ E S x hx s H j K hk hs
     have hK:ContinuousOn (fun y:Points n=>‖iteratedFDeriv ℝ j (expectP x) y‖) K:=by intro y hy; exact (((scented x (j+1) y (hs hy)).differentiableAt_iteratedFDeriv (Nat.cast_lt.mpr (Nat.lt_succ_self _))).continuousAt.norm).continuousWithinAt
     obtain ⟨B,hB⟩:= (hk.image_of_continuousOn hK).bddAbove; let T:=max B 0; have ht:0 ≤T:=le_max_right ..; refine ⟨m,A+T, add_nonneg hA ht,?_⟩; filter_upwards [hv] with i hi y hy; unfold errorP; rw [iteratedFDeriv_sub_apply (livingZ hQ E S x s _ _ _ (hs hy)) (scented x _ _ (hs hy)), add_mul]; exact (norm_sub_le ..).trans (add_le_add (hi _ hy) ((le_trans (hB ⟨_,hy,rfl⟩) (le_max_left ..)).trans (le_mul_of_one_le_right ht (one_le_pow₀ (E.charge _)))))
omit hQ H s hx
lemma advanceP(k:ℕ)(y:Points n): ∃ f:Fin n→ Cover, dist (points ((E.B k).qR (E.B k).ℓ ∘ f)) y≤ (n+1:ℝ)*2* (E.B k).mesh:=by
     let A:=E.B k; let d:=A.mesh; have hd:0<d:= (E.trueK k).Γ.rising
     let f(j:Fin n):= Needle.bead d (y j); let F:= points (A.qR A.ℓ ∘ f); let S:=F-y
     have hp(j:Fin n): ‖(F-y) j‖ ≤ 2*d:= by have h:= smoothV hd (y j); rw[dist_eq_norm] at h; exact h
     have hb:S=F-y:=rfl
     refine ⟨f,?_⟩; rw[dist_eq_norm]
     change ‖S‖≤_*_*d; apply le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ; rw[PiLp.norm_sq_eq_of_L2]; apply le_trans (sum_le_sum (fun i _=> pow_le_pow_left₀ (norm_nonneg _) (hp i) 2)); simp only[sum_const,nsmul_eq_mul, card_univ,Fintype.card_fin]; nlinarith [show (2*d)^2+(0:ℝ) ≥0 from by positivity, Nat.cast_nonneg (α:=ℝ) n]
local notation "X"=> Points n
variable (hv:Troupe E S)
include s H hQ hv hx
set_option maxHeartbeats 820000 in
lemma ontoW : YM.Sprig.Video.rapid E.cc (conf n) (errorP E S x) 0:=by
    intro K hK hk n₀ ε he
    obtain ⟨t,hp,hs⟩:= hK.exists_cthickening_subset_open (conf_open n) hk
    let P':= Metric.cthickening t K; have hT:IsCompact P':= hK.cthickening
    obtain ⟨m,A,hA,hv'⟩:= errs hQ E S x hx s H 1 P' hT hs
    let e(i:ℕ):= E.cc i; let f(i:ℕ):= (n+1:ℝ)*2* (E.B i).mesh
    have h:Tendsto (fun i=>(E.B i).mesh) atTop (𝓝 0):= by simpa only [pow_zero,one_mul] using E.neighbors 0
    have hh:Tendsto f atTop (𝓝 0):=by simpa only [mul_zero] using h.const_mul ((n+1:ℝ)*2)
    have hp': Tendsto (fun i=> A*(e i)^(n₀+m)*f i) atTop (𝓝 0):=by
           have h:= (E.neighbors (n₀+m)).const_mul (A*((n+1:ℝ)*2)); rw [mul_zero] at h; exact h.congr fun i=>by unfold f e; ring
    filter_upwards [hh.eventually_le_const hp,hv',hp'.eventually_le_const (half_pos he),hv.awake n x hx P' hT hs n₀ (ε/2) (half_pos he)] with i hi hh h' hL y hy
    obtain ⟨f',ht⟩:= E.advanceP i y; let z:=points ((E.B i).qR (E.B i).ℓ ∘ f'); have hB: Metric.closedBall y t ⊆ P':= fun x hx=> Metric.mem_cthickening_of_dist_le x y _ _ hy (mem_closedBall.mp hx); have ht':z∈ Metric.closedBall y t:= mem_closedBall.mpr (ht.trans hi);
    have hu:=hL f' (hB ht'); rw [norm_iteratedFDeriv_zero]; let b:=E.errorP S x i; have hP : ‖b y-b z‖ ≤ A*(e i)^m*f i:=by
            apply le_trans _ (mul_le_mul_of_nonneg_left (show ‖y-z‖ ≤ f i by rw[← dist_eq_norm,dist_comm]; exact ht) (mul_nonneg hA (pow_nonneg (zero_le_one.trans (E.charge i)) _)))
            exact (convex_closedBall ..).norm_image_sub_le_of_norm_fderiv_le (fun w hw=>(period hQ E S x hx s H _ 1 w (hs (hB hw))).differentiableAt (by simp)) (fun w hw=>by rw [← norm_iteratedFDeriv_one]; exact hh w (hB hw)) ht' (mem_closedBall_self hp.le)
    have hh:δ i^n₀*‖b y-b z‖ ≤ ε/2:= (mul_le_mul_of_nonneg_left hP (pow_nonneg (zero_le_one.trans (E.charge i)) n₀)).trans (by rw [pow_add] at h'; unfold e at *; nlinarith only[h']); calc
        _ ≤ δ i ^ n₀ * (‖b y-b z‖+‖b z‖):= mul_le_mul_of_nonneg_left (sub_le_iff_le_add.mp (norm_sub_norm_le (b y) (b z))) (pow_nonneg (zero_le_one.trans (E.charge i)) n₀)
        _ ≤ ε := by rw [mul_add]; exact (add_le_add hh hu).trans (add_halves _|>.le)
lemma momentsD(j:ℕ): YM.Sprig.Video.rapid E.cc (conf n) (errorP E S x) j:= YM.Sprig.Video.here _ (E.charge) E.climb _ _ (conf_open _) (fun k y h j=>period hQ E S x hx s H k j y h) (fun K hk hs j=>errs hQ E S x hx s H j K hk hs) (ontoW hQ E S x hx s H hv) j
end Canopy
end YM.Intag.Sprig
#print axioms YM.Intag.Sprig.Canopy.momentsD
