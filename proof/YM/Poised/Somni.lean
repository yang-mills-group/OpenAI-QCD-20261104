import YM.Poised.Pollen
/-!
# Lens panelized. Ward observations for short/near.[F2/W1].Budgets at B.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Lattice Wilson RG Source Source.Drops MeasureTheory Finset WardBin Work.G05 Planned.PrimaryIntegral295
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
variable {B A X E : Type}{d a k n m r:ℕ}{c l:Side}
namespace Pipes
open Set Cedar Ember Oval Cove Creek Stew PhysicalNext.JointLoad MultiNext.SignedSource MultiNext.SignedSource.Lyre Place Lining Lining.Ferry
open YM.Next.Free Pressure Garden QCD.Fork Leaf Tee Flume Kit Run Laurent Heir AnalyticBridge.SectorAffine.Offset Planned.AtomRegular Push.Uniform
variable [Fintype A][Fintype B]{f:A→ℝ}{g:B→ℝ}{w x a' p u v τ:ℝ}{o:Site c}
def mantel (d:ℕ)[DecidableEq A] : Alg A →L[ℝ] Alg A:= (panel d).toContinuousLinearMap.restrictScalars ℝ
lemma Pika (X: A→ B→ℂ)(n:ℕ)[DecidableEq A][DecidableEq B](x:Alg A): mantel n (changeVars X x)=changeVars X (mantel n x):=by
   rw [← write x]; unfold mantel; change panel n (changeVars X _)=_; simp only [map_sum]; refine sum_congr rfl fun i _=>?_ ; rw [map_smul,map_smul,past _ _ (show changeVars X (mono i)∈ layer _ i.card from exterior_layer _ (homogeneous ..))]; change _=changeVars X (panel _ _); rw [map_smul,past _ _ (homogeneous ..)]; split; · rw [map_smul] -- sintDec
   rw [smul_zero,smul_zero,map_zero]
lemma region_mantel [DecidableEq A](U:Finset A)(d:ℕ)(x:Alg A)(hx:x∈region U): mantel d x∈region U:=by
   unfold mantel; change (panel d x)∈_; -- direct term
   unfold panel; change (∑ i:Finset A,_ )∈region U; apply Subalgebra.sum_mem; intro i _; split; next h=>
       by_cases hv:i ⊆ U; · apply Subalgebra.smul_mem; obtain ⟨z,-,hh,H⟩:=expression i; rw [H]; refine Subalgebra.list_prod_mem _ (by simp only [List.mem_ofFn]; rintro _ ⟨j,rfl⟩; exact Creek.marked _ U (hv ((hh _).mpr ⟨j,rfl⟩)))
       rw [Cove.ember _ hx i hv, zero_smul]; exact Subalgebra.zero_mem _
   next _=> exact Subalgebra.zero_mem _
-- height-lens proof to Fence and projected jet annihilation
structure Flame (X:Grid c→Lat.Fields c 6)(η:BudgetPoint)(S:Support c)(o:Site c)(w:ℝ)(d m:ℕ)(τ:ℝ): Prop where
    sight : MassiveQCD.Plate.Sight S o 2 η w X τ
    issues i : i < m → η.supBounds o S (framesF (purseX o d w) ∘ (mantel i∘X)) τ
-- sup and null for all sufficiently small degrees.
variable (b:Cover) (X: Grid c→ Lat.Fields c 6) (he:∀ g U,Lat.slots 6 g (X (Lattice.gauge g U))=X U)
include he in
lemma inherent (i:ℕ)(g:Frame c)(U:Grid c) : Lat.slots 6 g ((mantel i) (X (Lattice.gauge g U)))=mantel i (X U):=by
   rw [← he g U]; exact (Pika (signs g) i _).symm
lemma crewR {η:BudgetPoint}{V:Support c} (h: Flame X η V o w d m τ)(i:ℕ): Rooted V (mantel i ∘ X) ∧ Ease.Charm η V (mantel i ∘ X) ∧ Measurable (mantel i ∘ X)∧ (∀ U,mantel i (X U)∈layer _ i):= by
    have hh:= (show Ease.Charm η V X from ⟨h.sight.room,h.sight.use⟩).scales (mantel i)
    exact ⟨⟨hh.1,fun U=> region_mantel _ _ _ (h.sight.gate U)⟩,hh,(mantel i).measurable.comp h.sight.borel,fun i=>chamber _ _⟩
lemma inherits (H: TaperHol)(hx:ContDiffAt ℝ n (X∘increment 1) 0) (h:∀ (J:Labels.Jet su)(t:ℕ), t<k → WardBin.leading t (Beacon.moment (d:=n) H b J X)=0) (i:ℕ)(hk:k≤n+1) :∀ (J:Labels.Jet su)(t:ℕ),t<k→WardBin.leading t (Beacon.moment (d:=n) H b J (mantel i ∘ X))=0:=by
    intro J t ht
    let A:= mantel (A:=Faces (UV.Multi n)) i; have he : Beacon.moment (d:=n) H b J (mantel i ∘ X)=A ∘ Beacon.moment (d:=n) H b J X:=funext fun x=>by unfold Beacon.moment; change changeVars _ _=_; exact (Pika ..).symm -- annotate
    obtain ⟨V,hV,h'⟩:= Beacon.obtainsD H b X hx
    rw [he]; apply leading_zero_iff.mpr; rw [Display.clm_step _ _ _ (ContDiffAt.of_le (h' J).1 (by exact_mod_cast Nat.le_of_lt_succ (ht.trans_le hk))), leading_zero_iff.mp (h J t ht), map_zero]
-- aura: movement.w orth normalization for heights only. map compact of g; preserve f weight row cap.Bounds
private theorem material (A:Side)(p:Site A)(n:ℕ)(w:ℝ)(k:Frame A) (i j: Faces (Site A)) : (purseX p n w i : ℂ)* signs k i j= signs k i j*(purseX p n w j :ℂ):=by
    obtain ⟨⟨x,i⟩,rfl⟩:= (stretch _).surjective i; obtain ⟨⟨y,j⟩,rfl⟩:= (stretch _).surjective j
    by_cases h:x=y; · subst y; unfold purseX; simp_rw [life]; rw [mul_comm (↑_:ℂ)] -- rw correct
    cases i <;> cases j <;> simp only [signs,stretch, Equiv.coe_fn_mk,Sum.elim_inl,Sum.elim_inr, Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₂₂,Matrix.fromBlocks_apply₁₂,Matrix.fromBlocks_apply₂₁,Matrix.zero_apply,Matrix.transpose_apply, Matrix.star_apply] <;> simp [Lat.rotates, Lat.copies, Matrix.blockDiagonal_apply,siteRot, rides,h,Ne.symm h] -- h.symm eq? h : ¬...
lemma frame_slots (A:Side)(p:Site A)(n:ℕ)(w:ℝ)(k:Frame A) (x:Lat.Fields A 6): framesF (purseX p n w) (slots 6 k x)= slots 6 k (framesF (purseX p n w) x):=by
    let L: Matrix (Faces (Site A)) _ ℂ:= signs k; let f:=purseX p n w; let P:Matrix (Faces (Site A)) _ ℂ:= @Matrix.diagonal _ _ (Classical.decEq _) _ (fun i=>(f i:ℂ)); change ((changeVars P).comp (changeVars L)) x= ((changeVars L).comp (changeVars P)) x; have h:P*L=L*P:=by ext1 i j; unfold P; rw [Matrix.diagonal_mul, Matrix.mul_diagonal]; exact material ..
    rw [← change_mul, ←change_mul,h]
end Pipes
end YM.Massive.Poised
