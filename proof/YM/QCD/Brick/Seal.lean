import YM.QCD.Brick.Nova
/-! # Tensor test at constant patch directions. Loft affine.R.Bound all marks. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Brick
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew AnalyticBridge.VerifiedReset Revolve
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c f:Side}{N:ℕ}{p:BudgetPoint}{X: Support f}{o:Site f}
open MultiNext.SignedSource YM.Next.Foundations
local notation "Ω"=> EvenA f N
def orbitL (V: Matrix (Modes f N) (Modes f N) ℂ):EvenA f N→L[ℝ] EvenA f N:= LinearMap.toContinuousLinearMap { toFun:= fun i=> sways V i,map_add':=fun i j=> map_add .., map_smul':=fun a x=> eSM _ (phare _) _ _ }
lemma relays {ι:Type}(Y:ι→ Sheet f)(p: Finset ι)(s:SampleX):locQ o s (∑ i∈p,Y i)=∑ i∈p,locQ o s (Y i):=by
   induction p using Finset.induction_on with
   | empty=> rw [sum_empty,sum_empty]; simp only [locQ,show ∀ x y:Site f,cell (0:Sheet f) x y=0 from fun _ _=>rfl,smul_zero,sum_const_zero]
   | insert i t hi ih=> rw [sum_insert hi,sum_insert hi,← ih]; suffices hh : ∀ X W,locQ o s (X+W)= locQ o s X+locQ o s W from hh ..
                        intro X W; unfold locQ; simp only [show ∀ x y:Site f,cell (X+W) x y=cell X x y+cell W x y from fun _ _=>rfl,smul_add,sum_add_distrib]
lemma directive {v: Directions su f} (h: Mom.screen X v∈ Mom.Maps o X 1): ∃ u:Axis→su.Color, Agrees X v (∑ i : Axis, rankD (u i) i):=by
   obtain ⟨z,hz,h⟩:=h; refine ⟨fun i=>z i 0,fun i hi hk=>?_⟩; have he:=h i; rw [Mom.screen_at, if_pos (show Mom.needed X i from ⟨hi,hk⟩),if_pos (show Mom.needed X i from ⟨hi,hk⟩)] at he
   have hv : z i.2 (Mom.stamp o i.1) =z i.2 0:= by simpa using! ((Mom.base (hz i.2)).2 (0:ℝ) (Mom.stamp o i.1)).symm -- fill
   rw [he, hv]; simp [Finset.sum_apply,rankD]
variable (A: Grid f→ EvenA f N)(hp: LocalOn X A)(hv:shadeG A)(hh:∀ U,Fit (A U))(ht:DifferentiableAt ℝ (A ∘ increment 1) 0)(hw:Nonwrapping X o)(hn:4≤f.val)(b:Flavor N)
variable (hq:∀ i, shape o (feeF b (A 1)) i=0)
include ht hh
lemma drip (d: Directions su f) : Fit (fderiv ℝ (A ∘ increment 1) 0 d):=by
   let g:= A ∘ increment 1; intro V hV; let L:=orbitL (flute (Lat.Row f) V)
   have hQ:L ∘ g=g:=funext (fun i=> hh (increment 1 i) V hV)
   change L ((fderiv ℝ g 0) d)=_
   rw [show L (fderiv ℝ g 0 d) = fderiv ℝ (L ∘ g) 0 d from (congr_arg (fun h:Directions su f→L[ℝ]Ω=>h d) ((L.hasFDerivAt (x:=g 0)).comp (f:=g) 0 ht.hasFDerivAt).fderiv).symm,hQ]
include hp hv hw hn hq
lemma dutyH (v:Directions su f)(h: Mom.screen X v∈ Mom.Maps o X 1):
    let T:= fderiv ℝ (A ∘ increment 1) 0 v
    lights o false (grasp T.val) :=by
   intro t i j; let d:=fderiv ℝ (A ∘ increment 1) 0; obtain ⟨p,h⟩:= directive h
   let x:= ∑ i:Axis,rankD (f:=f) (p i) i; let F:=(A ∘ increment 1)
   have he (v:Directions su f): HasDerivAt (fun t:ℝ=> F (t • v)) (d v) 0:= ht.hasFDerivAt.comp_hasDerivAt_of_eq 0 (show HasDerivAt (fun t:ℝ=>t • v) v 0 by simpa using (hasDerivAt_id' (0:ℝ)).smul_const v) (zero_smul ℝ v).symm
   have hT:t=d x:=by
       have hx:=he x; rw [show (fun t:ℝ=>F (t • x))=(fun t:ℝ=>F (t • v)) from ?_] at hx; exact (he v).unique hx
       funext i; exact hp (increment 1 (i • x)) (increment 1 (i • v)) (show Agrees X (increment 1 (i • x)) (increment 1 (i • v)) from fun k hk hj=> by change su.lieExp (i • x k) * 1=su.lieExp (i • v k) * 1; rw [show v k=x k from h k hk hj])
   refine ⟨?_,fun hx=> Bool.noConfusion hx⟩; rw [locales o (drip A hh ht v) b]; have h : locQ o none (feeF b t)=0:=by
       rw [hT]; change locQ o _ (meter b (d x))=_; dsimp only [x]; rw [map_sum,map_sum,relays]; apply sum_eq_zero; intro k _; exact cradle A hp hv hh ht hw hn b hq (p k) k
   rw [h]; split <;> rfl
end YM.QCD.Brick
