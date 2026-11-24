import YM.MassiveQCD.Column.Triangle
import YM.QCD.Fawn.Fleur

/-! # Gauge part of a pointed (only value-out at identity) column.

PointedSeed.fugue: At any issued play with true fixed Q choices through costs
and incident paths/Heir data, from the indicated one pre-L clock.
Assumes FULL (same) mask support read, no plugging fields at unflagged neighbors from a different sampling,
tested on plays (C,D). Proof following Piccolo at weaker weight.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Heir
open Function Filter Set Lattice Wilson Pressure Precision RG Tree Next Next.SectorChange Next.Fluctuations Next.Foundations
    Exterior Bloch Bid Push.SectorMeasure MultiNext.SignedSource MultiNext.SignedSource.Banjo WardBin.Lies Planned.AtomRegular
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {Pt : Teller G} {k : S.Choices} {V : Config G c} {F : Forest S.ratio}
    {P B : BudgetPoint} {o : Site f} {g : Site c → G.El} {X : Support f} {Y : Support c} {Q C M r t x τ : ℝ} {I : Type}
    {A : Stores S} {n l : ℕ} {D : Slab G c l} {q : Chi} {d u : ℝ} {f' : Config G f → ℝ}

section prof
variable (Q' : Rights G n) (hG : G.Simple) (a : Museum F x A X Y I) [Fintype I] (b : Folio.Bulletin x Pt T) (hr : Weft G S.patch.L P B Q C x)
    (hT : Act T F x k n r Q) (hq : Canvas P (S.ratio.parent o) (reach x) V g n C) (hC : 1 ≤ C) (hh : Matins T F B.power (2*C) M)
    (hQ : 1 ≤ Q) (hM : 1 ≤ M) (hk : 5 ≤ n) (hK : n ≤ B.order) (hF : 100*(1+radiusB x) ≤ c.val)
    (hP : P.threshold=temp x) (ht : temp x ≤ 2*B.threshold) (hpow : P.power ≤ B.power)
    (h' : loom P (reach x) C < r) (hy : Q*loom P (reach x) C ≤ 1)
    (hS : Short S B X) (he : PointedSeed B o X f') (hE : B.supBounds o X f' τ)
    (h : ∀ i, P.dirBound (S.ratio.parent o) (D i)) (hl : l ≤ n)
    (U : Config G f) (w : Prices G I) (hU : Healthy B.threshold X (a.received k T q d u V U w))
    (hu : 0 ≤ u) (hw : u*‖tape w‖ ≤ loom P (reach x) C)

include hG b hr hT hq hC hh hQ hM hk hK hF hP ht hpow h' hy hS he hE h hl hu hw hU

lemma PointedSeed.motif : let f₀ (V : Config G c) := f' (a.received k T q d u V U w)
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
  refine (slots_bound (U:=z) hg hf hj (C:=(n+1:ℝ)*((3*K)^n*((S.patch.L.val:ℝ)⁻¹)^4)*Q'.fee*τ) (by positivity) (fun p v hv => he.profile hG (short_nonwrap hS hr.cover hF he.site) (le_trans (by decide : 2 ≤ 4) hn) hE (by positivity)
    (inv_le_one_of_one_le₀ (Nat.one_le_cast.mpr S.patch.L.property)) hK' Q' hK _ h0 he' hz (le_trans (by decide : 4 ≤ 5) hk) (p.length_le.trans hj) _ (fun i => h _ ((p.partSize_le i).trans hj) _ (fun k => hv _)))).trans_eq ?_
  unfold shortFee; rw [mul_pow (3:ℝ)]; ring
end prof
section songs
open AnalyticBridge.LocalGaussian.Moments
variable {Z : Slab G c l} {N : Libretto G n} {E : Record}
variable (b : PointedSeed B o X f') (e : G.Simple) [Fintype I]
    (a₀ : Museum F x A X Y I) (q': Plays N E P B Pt T x)
variable {Γ : Prices G I → ℝ} (hk: 5 ≤ n)(ha:Healthy P.threshold Y V) (ht:B.supBounds o X f' τ)(hu:0≤u)(hS:Short S B X) (hA:Silences G I n u (E.ε*B.threshold) Γ)
    (U:Config G f)(i:ℕ)(k q d)
include e hk q' b hS ha ht hu hA
set_option maxHeartbeats 650000 in
lemma PointedSeed.fugue : Hera.Fugue a₀ U f' T N E P B i Γ u (τ * Lute.phrase N * ((S.patch.L.val:ℝ)⁻¹)^4) k q d o V:=by
    intro Z hz
    have hd:= q'.rehearsed
    have hP:= hd.temp_eq; have hT:= hd.tensions; have hF:= q'.space
    obtain ⟨g,hg⟩ := framed a₀ ha hF (by omega) (Z:=N.Z) hd.wire
    have hb := q'.bulletin; have hacts:=q'.acts F k
    have hw := hA.stay Z hz
    have hY := hT.small.trans (min_le_right ..)
    have hw' := hw.trans hT.noise
    have hW := border_healthy q'.sew N.width N.price hd.early hacts E.majorant (by omega) hT a₀ hb N.Z rfl hd.wire hF hP ha U Z hu hw B.threshold_pos (q:=q) (d:=d)
    refine ⟨a₀.joint_receives hacts hb hg U N.C_one hT.allows (fun g => (a₀.extra_size g u hu Z).trans hw') b.good hd.orders hW,?_⟩
    intro j hj A hD
    obtain ⟨g,hg⟩:=a₀.canvas o (Finset.mem_union_left _ b.site) ha hF N.Z (by omega) hd.wire
    apply ((b.motif N.rights e a₀ hb hd.weft hacts hg N.C_one (q'.stages F) E.majorant N.matins hk hd.orders hF hP hT.coarse hd.powers hT.allows hY hS ht hD hj U Z hW hu hw').2 j hj).trans
    let ρ:=(S.patch.L.val:ℝ)⁻¹; have hρ:0 < ρ:= by unfold ρ; positivity
    let pricesX := (N.M+ tranche S.patch.L n E.Q (loom P (reach x) N.C) (u*‖tape Z‖) B.threshold)^n
    let z := (Lute.leading N+Lute.rust N E P B S.patch.L X i x u *powers Z^2)^n
    have hvq:= Lute.pay_le (C:=N) (D:=E) (P:=P) (B:=B) (L:=S.patch.L) (X:=X) (r:=i) (x:=x) hu Z
    rw [Plays.price,if_pos (show coverNumber _ X^3 < S.patch.L.val from hS),Lute.decay,if_pos (show coverNumber _ X^3 < S.patch.L.val from hS)] at hvq
    change shortFee _ * pricesX * ρ^5 ≤ Lute.phrase N * ρ^5 * z at hvq
    rw [mul_right_comm (Lute.phrase _)] at hvq
    have hh:=le_of_mul_le_mul_right hvq (by positivity : 0 < ρ^5)
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh (by positivity : 0 ≤ ρ^4)) ht.1).trans_eq (by unfold z ρ; ring)
end songs
end YM.PhysicalNext.JointLoad.Heir
