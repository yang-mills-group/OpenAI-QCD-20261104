import YM.Poised.Caret
/-! Fiery directions. Guage span passport and normalized direction payer. Preserve .route tape choice at actual. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Lattice Wilson RG Source Source.Drops MeasureTheory Finset WardBin Work.G05 Planned.PrimaryIntegral295
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
variable {B A X E : Type}{d a k n m r:ℕ}{c l:Side}
namespace Pipes
open Set Cedar Ember Oval Cove Creek Stew PhysicalNext.JointLoad MultiNext.SignedSource MultiNext.SignedSource.Lyre Place
variable (P:BudgetPoint) (V:Support c) (b:Cover) [Fintype B] (x: Directions su c)
variable (f : Faces (Site c) → ℝ) (g:B→ℝ){p C t:ℝ}
lemma charged {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E](n:ℕ): Powers.space E4 E n ≤ rangeLt E (n+1):=by unfold Powers.space; apply Submodule.span_le.mpr; intro f hf; obtain ⟨i,hi,hf⟩:=hf; exact exact_le_band (Nat.lt_succ_of_le hi) (can_write.mpr ⟨_,Powers.tensor_form hf⟩)
lemma inL_bu (h:Mom.screen V x∈ Mom.Maps (wrap c b) V (a+1)): Buoyant (B:=B) (x,0) V b (2*(a+1)):=by
   obtain ⟨f,hf,h⟩:=h
   refine ⟨⟨fun i j=>f j i,show (fun i j=>f j i)∈_ from ?_,fun i hi=>?_⟩,(Buoyant.inertV (B:=B) V b).2⟩
   · rw [show 2*(a+1)/2=a+1 from by omega]; exact vector_band _ fun j=> charged a (by simpa using hf j)
   specialize h i; rw [Mom.screen_at, if_pos hi,if_pos hi] at h; exact h
lemma inL_R (h: Sized C x P (wrap c b)) : Venture f g (P:=P) (o:= wrap c b) C (x,0):=⟨h,⟨h.1,fun i=>by change ∑ j, ‖orderR f g 0 i j‖≤ C; simp [orderR,h.1]⟩⟩
lemma magnet (h:Banjo.Promise d C t P (wrap c b) V x)(he:t=p^2)(hp:0<p)(hp':p≤1)(hC:0 ≤ C)(hK:k≤ 2*d+2) : Heritage P V b f g k (x,0) p ((d+1:ℕ)*C):=by
    obtain ⟨z,hz,h,h'⟩:=h; let R(i:Fin (d+1)):Path c B:= (z i,0)
    have hs: ∑ i,R i=(x,0):=Prod.ext (by rw [Prod.fst_sum]; exact hz.symm) (by rw [Prod.snd_sum]; simp [R])
    have he':= assembleH (k:=k) P V b f g univ R (fun i=>2*(i.val+1)) (fun i=> by omega) (fun i=> inL_R P b (z i) f g (show Sized _ _ _ _ from by rw [pow_mul, ← he]; exact h i)) (fun i hi=> inL_bu V b (z i) (h' i (by omega))) hp hp' hC
    rw [card_univ,Fintype.card_fin,hs] at he'; exact he'
lemma patchup (p C:ℝ)(X Y: Directions su c)(hv: Sized (C*p^(max k 2)) (X-Y) P (wrap c b))(hp:0<p)(hp':p≤1)(hC:0≤C)(hY:Heritage P V b f g k (Y,0) p t): Heritage P V b f g k (X,0) p (C+t):=by
    have hh:= residual P V b (X-Y,0) f g (inL_R P b (X-Y) f g hv) hC hp hp'
    rw [show ((X,0):Path c B)= (X-Y,0)+(Y,0) from by simp]; apply Heritage.plusK _ _ _ _ _ _ _ hh hY
-- normalization with σ
open Heir Banjo Tree Pressure Precision
variable {p0: ℕ} {S:StepData c l}{T:Tube su S}{Q:Teller su}
lemma boxed_sq (L:Side): (L.val:ℝ)⁻¹ = Kit.slope L^2:=by unfold Kit.slope; rw [inv_pow, Real.sq_sqrt (by positivity)]
lemma boxed1 (L : Side): 0 < Kit.slope L ∧ Kit.slope L ≤1:= by
   have hh:1≤ (L.val:ℝ):= by exact_mod_cast L.property
   exact ⟨by unfold Kit.slope; positivity,inv_le_one_of_one_le₀ (by simpa using (Real.sqrt_le_sqrt hh))⟩
/-- Untapered Hive.Cost.Wait for L.Controls only on the certified flight. -/
lemma initial (Z:Teller su)(d K:ℕ)(M:ℝ)(hP:0<M)(hv:d ≤ K)(he:d ≤ Z.j-2) : ∃ C:ℝ,1≤C ∧ ∀ (l c:Side)(P:BudgetPoint)(V:Support l)(S: StepData c l)(T: Tube su S), Z.Funds S T→ P.power=K → Odd S.patch.L.val →∀ (o:Cover)(X:Directions su c), Limb K (S.ratio.parent (wrap l o)) X (M*P.threshold) → ∀ (k:ℕ), k≤2*d+2 →∀ {B:Type}[Fintype B] (f: Faces (Site l)→ℝ)(g:B→ℝ), Heritage P V o f g k (route T X,0) (Kit.slope S.patch.L) C:=by
   obtain ⟨C,hC,h⟩:= Newt.row_home su Z.width Z.C d K; obtain ⟨A,hA,H⟩:= Newt.canal su d K hv -- likely args d P
   refine ⟨1+ (d+1:ℕ)*(A*C*M),le_add_of_nonneg_right (by positivity),?_⟩
   intro l c P V S T hZ hK hO b X hX k hk B zB f g
   let L:=S.patch.L; have ht : T.R.Deep Z.η Z.C d:=⟨hZ.crosses.1,hZ.crosses.2.1,hZ.crosses.2.2.1,fun k hk=> hZ.crosses.2.2.2 k (hk.trans (by have := hZ.atStep; omega))⟩
   let Y : Directions su c := M⁻¹ • X
   let W:= YM.Next.SectorChange.Flat.labels Y; obtain ⟨hp,hp'⟩:=boxed1 L; have hL:1 ≤ (L.val:ℝ):=Nat.one_le_cast.mpr L.property
   have hs: Newt.blown C P (L.val:ℝ) d (wrap l b) (route T Y):=by
      rw [show Heir.route T Y=Newt.roll su S.ratio T.R W from funext fun i=>Heir.roll_as Y (main T) i]
      refine h _ _ S.ratio T.R ht P (wrap l b) hO hK W (fun i=>?_); change ‖M⁻¹ • X _‖ ≤ _; rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr hP).le]; apply (inv_mul_le_iff₀ hP).2 ((hX _).trans_eq (mul_assoc ..))
   obtain ⟨w,hw,hv,hv'⟩:= H l V (wrap l b) P (L.val:ℝ) C _ hK hL (zero_le_one.trans hC) hs
   have hZ:Banjo.Promise d (A*C*M) ((L.val:ℝ)⁻¹) P (wrap l b) V (route T X):=by
      refine ⟨fun i=> M • w i,?_,?_,?_⟩
      · rw [← smul_sum,←hw,show Y= M⁻¹ • X from rfl,map_smul, smul_inv_smul₀ hP.ne'] -- Y not unfolded
      · intro i; refine ⟨by positivity,fun j=>?_⟩; change ‖M • w i j‖ ≤ _; rw [norm_smul,Real.norm_of_nonneg hP.le]; exact (mul_le_mul_of_nonneg_left ((hv i).2 j) hP.le).trans_eq (by unfold L; ring)
      intro i hi; rw [map_smul]; exact (Mom.Maps ..).smul_mem _ (hv' i hi)
   exact Heritage.weak P V b _ f g (magnet P V b _ f g hZ (boxed_sq _) hp hp' (by positivity) hk) (le_add_of_nonneg_left zero_le_one) hp.le
end Pipes
end YM.Massive.Poised
