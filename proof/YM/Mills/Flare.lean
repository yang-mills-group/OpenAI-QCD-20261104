import YM.Mills.Vivid
/-! # Taking stamped powers (physics coefficient, right-blade convention)
 relative exponent ISSUANCE financed. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.FlareV
open Function Lattice Wilson QCD Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph QCD.GasP PhysicalNext.Repeat.Turn Patron Kites Ribbon Cupola Relight Stew Reggae
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N:ℕ} {J K A B R U I:Type} [Fintype I]
open Stitch Plate
local notation "X"=> Ribbon.Spine I
local notation "Z"=> Keys c N

variable [Fintype A]
noncomputable def weighs (w:A→ℝ) : Alg A→ₐ[ℂ] Alg A:=changeVars (Matrix.diagonal (fun i=>(w i:ℂ)))
noncomputable def tollCard (w:I→ℝ)(i:Spine I):ℝ:= if i.1.2=false∧i.2=0 then w i.1.1 else 1
noncomputable def ignites (w:I→ℝ)(u:Finset (Spine I)) := ∏ i∈u,(tollCard w i:ℂ)
noncomputable def roomKey (w:I→ℝ) :A⊕ Ribbon.Spine I→ℝ:= Sum.elim (fun _=>1) (tollCard w)
noncomputable def capstone (A:Type)[Fintype A](w:I→ℝ): Patio (A⊕Spine I)→ₐ[ℂ] Patio (A⊕Spine I) := car (weighs (roomKey w)) fun _x h=> by unfold weighs; exact (exterior_parity _ _).trans (congr_arg _ h) -- car?
local notation "V"=> Patio (A⊕Spine I)
variable (w:I→ℝ)(T:Finset I) (q:I→Bool)(u: Finset (Ribbon.Spine I))
lemma hall (w:A→ℝ)(s:Finset A)(x: Alg A): coef s (weighs w x)=(∏ i∈s,(w i:ℂ))*coef s x:=by
    change coef s (wscale w x)=_; rw [Creek.wax,map_sum,sum_eq_single s]
    · rw [map_smul,map_smul,Grass.read]; change coef s x *(_*1)= _; rw [mul_one,mul_comm]
    · intro j _ he; rw [map_smul,map_smul, Grass.read_other _ _ he.symm,smul_zero,smul_zero]
    simp
lemma patrol (x:V) : pluck A u (capstone A w x)=ignites w u • pluck A u x:=by
     change scrape A u (weighs (roomKey w) x.val)= _; change scrape A u _=ignites w u • scrape A u x.val; rw [pokes,pokes, smul_sum]; refine sum_congr rfl (fun i _=>?_); rw [hall,mul_smul]; unfold roomKey; rw [Finset.prod_disjSum]; simp only [Sum.elim_inl,Complex.ofReal_one,Finset.prod_const_one,Sum.elim_inr,one_mul]; -- may no goals
     rfl
lemma patrol_open (x:V)(s:Finset I)(h:Polite q s x): capstone A w x= (ignites w (burst q s)) • x:=by
    apply pluckVisible; intro i; rw [patrol,map_smul]; by_cases hv:i=burst q s; · rw [hv]
    rw [show pluck _ _ x=0 from h.spectral _ hv, smul_zero, smul_zero]
omit [Fintype I] in
lemma oneBeat (i:I) : ignites w (burst q {i})=(w i:ℂ):=by
    unfold ignites; rw [prod_eq_single ((i,false),0),show tollCard _ _=_ from (if_pos ⟨rfl,rfl⟩ : tollCard w ((i,false),0)=w i)]; · intro j hj h; have hh:j.1.1=i:= mem_singleton.mp (located q ({i}:Finset I) j hj); have hx: ¬(j.1.2=false ∧ j.2=0):= fun hv=> h (Prod.ext (Prod.ext hh hv.1) hv.2); rw [show tollCard w j=1 from if_neg hx,Complex.ofReal_one]
    exact fun h=> False.elim (h ((Ribbon.place q ..).1 (mem_singleton_self i)))
noncomputable def give := ∏ i∈ T,(w i:ℂ)
omit [Fintype I] in
lemma attuned : ignites w (burst q T)=give w T:=by
    induction T using Finset.induction_on with
    | empty => simp [ignites,give]
    | insert i s hi hs=>
       rw [← singleton_union,pulver]; have hr: Disjoint ({i}:Finset I) s:=by simpa using hi
       unfold ignites; rw [prod_union ((crossedR q ..).2 hr)]; unfold give; rw [prod_union hr, prod_singleton]; exact congr_arg₂ (·*·) (oneBeat w q i) hs
lemma partTone (g:Patio A): capstone A w (rootR X A g)=rootR X A g:=by -- unused N
    apply pluckVisible; intro i; rw [patrol]; by_cases hi:i=∅; · rw [hi]; unfold ignites; rw [prod_empty,one_smul]
    rw [show pluck A i (rootR X A g)=0 from (by change scrape A i (Ribbon.fiber X g.val)=0; rw [←quiet,stakesX,if_neg hi]),smul_zero]
end YM.MassiveQCD.FlareV
