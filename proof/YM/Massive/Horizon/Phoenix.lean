import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Sonata
import YM.Massive.Horizon.Candle
/-! Short output prices without plaquette annihilation, adapted Motif & Piccolo. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Heir
open Function Filter Set Lattice Wilson Pressure Precision RG Tree Next Next.SectorChange Next.Fluctuations Next.Foundations
    Exterior Bloch Bid Push.SectorMeasure MultiNext.SignedSource MultiNext.SignedSource.Banjo WardBin.Lies Planned.AtomRegular
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {Pt : Teller G} {k : S.Choices} {V : Config G c} {F : Forest S.ratio}
    {P B : BudgetPoint} {o : Site f} {g : Site c → G.El} {X : Support f} {Y : Support c} {Q C M r t x τ : ℝ} {I : Type}
    {A : Stores S} {n l : ℕ} {D : Slab G c l} {q : Chi} {d u : ℝ} {f' : Config G f → ℝ}

variable (Q' : Rights G n) (hG : G.Simple) (a : Museum F x A X Y I) [Fintype I] (b : Folio.Bulletin x Pt T) (hr : Weft G S.patch.L P B Q C x)
    (hT : Act T F x k n r Q) (hq : Canvas P (S.ratio.parent o) (reach x) V g n C) (hC : 1 ≤ C) (hh : Matins T F B.power (2*C) M)
    (hQ : 1 ≤ Q) (hM : 1 ≤ M) (hk : 4 ≤ n) (hK : n ≤ B.order) (hF : 100*(1+radiusB x) ≤ c.val)
    (hP : P.threshold=temp x) (ht : temp x ≤ 2*B.threshold) (hpow : P.power ≤ B.power)
    (h' : loom P (reach x) C < r) (hy : Q*loom P (reach x) C ≤ 1)
    (hS : Short S B X) (he : Seed3 B o X f') (hE : B.supBounds o X f' τ)
    (h : ∀ i, P.dirBound (S.ratio.parent o) (D i)) (hl : l ≤ n)
    (U : Config G f) (w : Prices G I) (hU : Healthy B.threshold X (a.received k T q d u V U w))
    (hu : 0 ≤ u) (hw : u*‖tape w‖ ≤ loom P (reach x) C)

include hG b hr hT hq hC hh hQ hM hk hK hF hP ht hpow h' hy hS he hE h hl hu hw hU

lemma motif3 : let f₀ (V : Config G c) := f' (a.received k T q d u V U w)
    let K := M+tranche S.patch.L n Q (loom P (reach x) C) (u*‖tape w‖) B.threshold
    ContDiffAt ℝ n (f₀ ∘ journey V l D) 0 ∧ ∀ j ≤ n, ‖iteratedFDeriv ℝ j (f₀ ∘ journey V l D) 0‖ ≤ shortFee Q' * K^n * ((S.patch.L.val:ℝ)⁻¹)^4 * τ := by
  intro f₀ K
  have hw' := (a.extra_size g u hu w).trans hw
  have hK' : 1 ≤ K := le_trans hM (le_add_of_nonneg_right (tranche_nn _ _ (by positivity) (mul_nonneg hu (norm_nonneg _)) B.threshold_pos.le))
  let L := enters V (S.ratio.parent o) (reach x) g D (a.extra g u w)
  let z := display T F x k true ∘ L; let fSide := f; let f := f' ∘ increment (1:Config G _)
  obtain ⟨he',hz⟩ := plucked a b hr hT hS hq he.site hC h' U w hw' D hQ (by omega) hy hU
  have hf : ContDiffAt ℝ n f (z 0) := (along he.good (by simpa only [one_smul,z,Function.comp_apply,L] using hz 1 (by simp))).of_le (Nat.cast_le.mpr hK)
  have hs := (depicted (q:=q) (d:=d) a b hr hT hS hq he.site hC h' U w hw' D)
  have hs : f ∘ z =ᶠ[𝓝 0] f₀ ∘ journey V l D := by
    filter_upwards [hs] with i hi; exact (he.good.sites _ _ (agrees_mono hi (fun _ hv => Finset.mem_union_left _ hv))).trans ((he.good.symmetry _ _).trans (he.good.symmetry ..))
  have hE' : loom P (reach x) C ≤ 1 := le_trans (le_mul_of_one_le_left ((mul_nonneg hu (norm_nonneg _)).trans hw) hQ) hy
  have hg := (timesEnter hq hT hP (by omega) h hC hl hQ hE' h'.le hw' true).1
  have h (j) (hj : j ≤ n) := first_promise (X:=X) hh hq ht hP hpow hC hl h hE' hT hQ hM (by omega) h'.le hw' (a.extra_size g u hu w) hj
  refine ⟨(hf.comp (f:=z) _ hg).congr_of_eventuallyEq hs.symm,fun j hj => ?_⟩
  have h0 : Promise 2 K ((S.patch.L.val:ℝ)⁻¹) B o X (z 0) := by
    simpa only [iteratedFDeriv_zero_apply] using h 0 (Nat.zero_le _) 0 (by simp)
  have hn : 4 ≤ fSide.val := S.sizes ▸ Nat.le_trans (show 4 ≤ c.val by omega) (Nat.le_mul_of_pos_right _ S.patch.L.property)
  rw [← (hs.iteratedFDeriv (𝕜:=ℝ) j).eq_of_nhds]; have hlarge := Q'.large; have hτ := hE.1
  refine (slots_bound (U:=z) hg hf hj (C:=(n+1:ℝ)*((3*K)^n*((S.patch.L.val:ℝ)⁻¹)^4)*Q'.fee*τ) (by positivity) (fun p v hv => ray3 hG he (short_nonwrap hS hr.cover hF he.site) hn hE (by positivity)
    (inv_le_one_of_one_le₀ (Nat.one_le_cast.mpr S.patch.L.property)) hK' Q' hK _ h0 he' hz hk (p.length_le.trans hj) _ (fun i => h _ ((p.partSize_le i).trans hj) _ (fun k => hv _)))).trans_eq ?_
  unfold shortFee; rw [mul_pow (3:ℝ)]; ring
end YM.PhysicalNext.JointLoad.Heir
namespace YM.PhysicalNext.JointLoad.Heir
open Function Filter Set Lattice Wilson Pressure Precision RG Tree Next Next.SectorChange Next.Fluctuations Next.Foundations
    Exterior Bloch Bid Push.SectorMeasure Planned.AtomRegular MultiNext.SignedSource WardBin.Lies Foliage
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {Pt : Teller G} {k : S.Choices} {V : Config G c} {F : Forest S.ratio}
    {P B : BudgetPoint} {g : outfit G f c} {X : Support f} {Y : Support c} {Q M C t r x z δ N ε τ : ℝ} {I : Type}
    {A : Stores S} {n j l : ℕ} {D : Slab G c l} {o : Site f} {u : ℝ} {q : Chi} {d : ℝ} {f' : Config G f → ℝ}

section pleas
variable (Q' : Rights G n) [Fintype I] (a : Museum F x A X Y I) (b : Folio.Bulletin x Pt T) (hT : Act T F x k n r Q)
    (h' : Matins T F B.power (2*C) M) (he : Seed3 B o X f') (hE : B.supBounds o X f' τ)
    (hQ : 1≤Q) (hC : 1≤C) (hM : 1≤M) (hn : 2≤n) (hl : l ≤ n) (hB : n ≤ B.order) (ht : P.threshold=temp x) (ht' : temp x ≤ 2*B.threshold) (hpow : P.power ≤ B.power)
    (hs : loom P (reach x) C ≤ 1) (hr : loom P (reach x) C < r) (hd : ∀ j, P.dirBound (S.ratio.parent o) (D j)) (U : Config G f) (w : Prices G I) (hu : 0 ≤ u)
include b hT h' he hE hQ hC hM hn hl hB ht ht' hpow hs hr hd hu

-- stage finance comes next, not conditional on evaluation point
omit hs hr hn hC ht' in
lemma short_fee3 (hS:Short S B X) (s : Seam T δ N) (hδ : 0<δ) (h₀ : 0≤N) (hG : G.Simple) (hL : licensed δ N S.patch.L)
    (Web : Web G) (Z : Collar G n) (hc : C=Cube.fee Z) (h : Tension Web δ Q ε x r (loom P (reach x) C) B.threshold)
    (hz : Cube.Wire P (reach x) Z) (hr : Weft G S.patch.L P B Q C x) (hn : 4≤n) (hF : 100*(1+radiusB x)≤c.val) (hV : Healthy P.threshold Y V)
    (hw : u*‖tape w‖ ≤ ε*B.threshold) :
    let f₀ (V : Config G c) := f' (a.received k T q d u V U w)
    let y := tranche S.patch.L n Q (loom P (reach x) C) (u*‖tape w‖) B.threshold
    let price := shortFee Q' * (M+y)^n * ((S.patch.L.val:ℝ)⁻¹)^4
    ContDiffAt ℝ n (fun z : Directions G c × Prices G I => f' (a.received k T q d u (increment V z.1) U z.2)) (0,w) ∧
      ContDiffAt ℝ n (f₀ ∘ journey V l D) 0 ∧ ∀ j ≤ n, ‖iteratedFDeriv ℝ j (f₀ ∘ journey V l D) 0‖ ≤ price * τ := by
  subst C; intro f₀ y price; obtain ⟨g,hp⟩ := framed a hV hF (by omega) hz; have hc := Cube.fee_one Z
  have hW := border_healthy s hδ h₀ hL hT hQ (by omega) h a b Z rfl hz hF ht hV U w hu hw B.threshold_pos (q:=q) (d:=d)
  have hw' := hw.trans h.noise; have hY := h.small.trans (min_le_right ..)
  refine ⟨a.joint_receives hT b hp U hc h.allows (fun g => (a.extra_size g u hu w).trans hw') he.good hB hW,?_⟩
  obtain ⟨g,hg⟩ := a.canvas o (Finset.mem_union_left _ he.site) hV hF Z (by omega) hz
  exact motif3 Q' hG a b hr hT hg hc h' hQ hM hn hB hF ht h.coarse hpow h.allows hY hS he hE hd hl U w hW hu hw'
end pleas
end YM.PhysicalNext.JointLoad.Heir
namespace YM.PhysicalNext.JointLoad.Heir
open Function Filter Set Lattice Wilson Pressure RG Precision Tree Next Next.SectorChange Next.Fluctuations WardBin.Lies
    Matrix Push.SectorMeasure SelectedOrderedKernels SelectedOrderedKernels.Sector Next.SectorChange.Rows Wisps
    Exterior Planned.AtomRegular.Foliage AnalyticBridge.NonflatCovarianceLocality.Placement
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {A : Stores S} {X : Support f} {Y : Support c}
    {V : Config G c} {P B : BudgetPoint} {ι : Type} [Fintype ι] [DecidableEq ι] {x u t τ : ℝ} {n l r : ℕ} {o : Site f}
    {q : Chi} {d : ℝ} {k : S.Choices} {f' : Config G f → ℝ} {Pt : Teller G}

variable {C : Libretto G n} {D : Record} (h : Plays C D P B Pt T x) (a : Museum F x A X Y ι)
    (he : Seed3 B o X f') (hV : Healthy P.threshold Y V)

namespace Plays
include h hV he
omit [DecidableEq ι] in
lemma short_prior3 (hX:Short S B X) (hG : G.Simple) (U : Config G f) (z : Prices G ι) (hu : 0 ≤ u) (hw : u*‖tape z‖ ≤ D.ε*B.threshold) (hτ : B.supBounds o X f' τ) :
    ContDiffAt ℝ n (fun z : Directions G c × Prices G ι => f' (a.received k T q d u (increment V z.1) U z.2)) (0,z) ∧
    ∀ l ≤ n, ∀ A : Slab G c l, (∀ j,P.dirBound (S.ratio.parent o) (A j)) →
      ‖iteratedFDeriv ℝ l (fun y => f' (a.received k T q d u (journey V l A y) U z)) 0‖ ≤ shortFee C.rights * (C.M + tranche S.patch.L n D.Q (loom P (reach x) C.C) (u*‖tape z‖) B.threshold)^n * ((S.patch.L.val:ℝ)⁻¹)^4 * τ := by
  obtain ⟨h0,hO,hP,h₁,h₂,hL,hW,ht,hf⟩ := h.rehearsed
  have H l (hl : l ≤ n) (A : Slab G c l) (hA : ∀ j,P.dirBound (S.ratio.parent o) (A j)) := short_fee3 (q:=q) (k:=k) (d:=d) C.rights a h.bulletin (h.acts F k) (h.stages F) he hτ
    D.majorant C.matins hl hO h₁ hP hA U z hu hX h.sew C.width C.price hG hL C.web C.Z rfl ht hW hf (by have := P.order_ge; omega) h.space hV hw
  exact ⟨(H 0 (Nat.zero_le _) 0 (fun j => j.elim0)).1,fun l hl A hA => (H l hl A hA).2.2 l hl⟩
end Plays
end YM.PhysicalNext.JointLoad.Heir
#print axioms YM.PhysicalNext.JointLoad.Heir.Plays.short_prior3
