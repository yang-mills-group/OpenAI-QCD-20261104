import YM.QCD.Pant.Inlet
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Stained
open ConnectedActivityE6
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {j n l k : ℕ} {R : Rep G f} {X : Coat T F} {I : Finset (Tubular f G)} {η r q a Y W d C' A b s μ C v B: ℝ} {Ñ : ChartRatio G}

private lemma vindance {ι : Type} [Fintype ι] [DecidableEq ι] {A H Z : Matrix ι ι ℝ} (hp : A*H=H*Z) (he : H*Hᵀ=1) :
    ∃ E : Body ι≃ₗᵢ[ℝ] Body ι, ∀ t, (E t).ofLp= H *ᵥ (WithLp.ofLp t) ∧ lens₀ A (E t)=lens₀ Z t := by
  let L := Matrix.toEuclideanLin H
  have hh w v : inner ℝ (L w) (L v)=inner ℝ w v := by
    simp_rw [PiLp.inner_apply,RCLike.inner_apply,starRingEnd_apply,star_trivial]; exact respects _ (mul_eq_one_comm.mp he) (WithLp.ofLp v) (WithLp.ofLp w)
  have ht : A.det= Z.det:= mul_right_cancel₀ (Matrix.isUnit_det_of_right_inverse he).ne_zero (by rw [mul_comm Z.det,← Matrix.det_mul,hp,Matrix.det_mul])
  have hz : Surjective (L.isometryOfInner hh) := by
    intro x; refine ⟨WithLp.toLp _ (Hᵀ *ᵥ x.ofLp),?_⟩
    change WithLp.toLp _ (H *ᵥ (Hᵀ *ᵥ x.ofLp))=x; rw [Matrix.mulVec_mulVec,he,Matrix.one_mulVec,WithLp.toLp_ofLp]
  let V:= LinearIsometryEquiv.ofSurjective _ hz
  refine ⟨V,fun t=> ⟨rfl,?_⟩⟩
  unfold lens₀; rw [ht,show (V t).ofLp= H *ᵥ t.ofLp from rfl,Matrix.mulVec_mulVec,reverses hp he, ← Matrix.mulVec_mulVec,
    respects _ (mul_eq_one_comm.mp he)]


lemma tiltsY (X:Coat T F)(h:P.Funds S T)(i:Finset (Bond f))(z:Site c→G.El) :
 let p:=lensS i G; let A:= Pond.circuit p X.relating; let Q:= Pond.circuit p (rinse X z).relating; ∃ V: Body (↥p)≃ₗᵢ[ℝ]Body (↥p), (∀ t, lens₀ Q (V t)=lens₀ A t) ∧ ∀ t,spill p (V t)=weep X z (spill p t):=by
  dsimp only
  let B:=lensS i G; let Y:=rinse X z; let E:= Hues.sheen X z; let H:=Pond.circuit B E
  let A:=Pond.circuit B X.relating; let Z:=Pond.circuit B Y.relating
  have he : Y.relating*E=E*X.relating := relatesG X z h
  have hB i j (hi:i∈ B) (hj:j∉ B) : E i j=0 ∧ E j i=0 := by
    have ht : i.1≠j.1 := by intro h; apply hj; refine mem_product.mpr ⟨h ▸ (mem_product.mp hi).1,mem_univ _⟩
    exact ⟨Rotation.off (z ∘ atEdge S) i j ht,Rotation.off (z ∘ atEdge S) _ _ ht.symm⟩
  have hs : Z*H=H*A := by
    change Batch.principal B _*Batch.principal B _= Batch.principal B _*Batch.principal B _
    rw [← Batch.localize_right (fun i hi j hj=> (hB j i hj hi).2), ← Batch.localize_left (fun i hi j hj=> (hB i j hi hj).1),he]
  have hh : H*Hᵀ=1 := by
    change Batch.principal B E*Batch.principal B Eᵀ=1
    rw [← Batch.localize_left (fun i hi j hj=> (hB i j hi hj).1),Rotation.upside, Batch.within_one]
  obtain ⟨V,hV⟩:= vindance hs hh
  have hg (t) : Pond.spill B (V t)=weep X z (Pond.spill B t) := by
    ext i; change (spill B (V t)) i= (E *ᵥ (spill B t).ofLp) i; simp only [Matrix.mulVec,dotProduct]
    classical
    rw [← Finset.sum_subset (subset_univ B) (f:=fun j => E i j*(spill B t).ofLp j) (fun j _ hj=> by simp [Pond.spill,hj])]
    by_cases h : i∈ B
    · have hh : (spill B (V t)) i=(V t).ofLp ⟨i,h⟩ := by simp [Pond.spill,h]
      rw [hh, (hV t).1, Matrix.mulVec, dotProduct, ← sum_attach B]; exact Finset.sum_congr rfl fun j _=> by simp [Pond.spill,j.2]; exact Or.inl rfl
    simp only [Pond.spill,WithLp.ofLp_toLp]
    rw [dif_neg h]; symm; apply sum_eq_zero; intro j hj; rw [(hB _ _ hj h).2,zero_mul]

  exact ⟨V,fun i=>(hV i).2,hg⟩
end YM.ConnectedActivityE6.Blaze.Stained
