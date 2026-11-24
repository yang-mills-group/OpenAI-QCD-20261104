import YM.TorusPCAC.Jet.ColorFilter
import YM.TorusPCAC.Jet.Rotation

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! # Exact label-space projection with Spin lift -/
set_option autoImplicit false
noncomputable section
namespace YM.TorusPCAC.Jet.Selector
open QCD QCD.Lat Finset Function MeasureTheory TensorProduct Set Spin
open scoped Matrix Topology BigOperators Kronecker TensorProduct Matrix.Norms.Frobenius

abbrev CM := Spin.MatrixColor.turn
abbrev MColor (i : Axis) := CM (Spin.mirror i)

abbrev overState {V : Type*} [AddCommGroup V][Module ℂ V] (F : Axis → V →ₗ[ℂ] V) (l : List Axis) : V →ₗ[ℂ] V := l.foldr (fun i f=> (F i).comp f) LinearMap.id
lemma state_next {V : Type*}[AddCommGroup V][Module ℂ V] (F : Axis → V →ₗ[ℂ] V) (l : List Axis) (i : Axis) (x : V) : overState F (i::l) x= F i (overState F l x):=rfl
variable (f : Axis→ℂ)

def travel := overState (V:=Pol) (fun i => average (f i) (Jet.rotate (mirror i)).toLinearMap)
def project := overState (V:=Spike) (fun i=> average (f i) (MColor i).toLinearMap)
lemma mirrorOver (i : Axis) (l : List Axis) (h : i∈l) (A : Spike) (hv : f i*f i=1) : MColor i (project f l A)= f i • project f l A:=by
  induction l with
  | nil=>cases h
  | cons a l ih=>
    unfold project; rw [state_next,half]; rcases List.mem_cons.mp h with ht|ht
    · subst a; simp only [AlgHom.toLinearMap_apply, map_add,map_smul]; rw [MatrixColor.twice]; rw [add_comm]; rw [smul_comm (f i),smul_add (f i),smul_smul (f i),hv,one_smul] -- test
    simp only [AlgHom.toLinearMap_apply,map_smul,map_add]
    change (2:ℂ)⁻¹ • (_ • MColor i (MColor a (project f l A))+MColor i (project f l A))=_
    rw [MatrixColor.parallel i a,ih ht, map_smul]; simp only [project]; rw [smul_comm (f i) 2⁻¹,smul_add (f i),smul_comm (f i) (f a)]

variable (i j : Flav) (a b : Order)
theorem survivor {g : Axis→ℂ} {B : Spike} (hb : IsUnit B) (hv : ∀ r, g r*g r=1) (hf : ∀ r, f r*f r=1)
    (ho : ∀ (A : Spike) r, Jet.rotate (Spin.mirror r) (crowd i j a b A) = g r • crowd i j a b (MColor r A))
    (he : ∀ r, MColor r B=(f r*g r) • B) (l : List Axis) (hl : ∀ i:Axis,i∈l)
    (A : Spike) : ∃ v : ℂ, travel f l (crowd i j a b A) = v • crowd i j a b B :=by
  let F r:= f r*g r; have h(l) : travel f l (crowd i j a b A)= crowd i j a b (project F l A):=by induction l with
    | nil=>rfl
    | cons i' l ih=> change overState _ _ _ = crowd i j a b (overState _ _ A); unfold travel project at ih; rw [state_next,state_next,ih]; simp only [half,AlgHom.toLinearMap_apply,ho,map_add,map_smul,F,mul_smul]
  have hT (i:Axis) : F i*F i=1:=by rw [show F i * F i=f i*f i*(g i*g i) by unfold F; ring,hv,hf,one_mul]
  obtain ⟨v,hv⟩:= MatrixColor.dimension (f:=F) (project F l A) _ hT (fun i=> mirrorOver F i l (hl i) A (hT i)) hb he; exact ⟨v,by rw [h,hv,map_smul]⟩

lemma entryMetric (u v : Pinor) : crowd i j a b (Matrix.single u v 1)=duo i j a b u v:=by unfold crowd; simp [Matrix.single,ite_smul, ite_and]
lemma firstR (v : Order) : deg v=0 → v=0:=by intro h; ext i; exact Nat.eq_zero_of_le_zero (h ▸ (show v i ≤ deg v from single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)))
lemma secondR (v : Order) (h:deg v=1):∃ a : Axis,v=hit a:=by
  by_contra! hv
  have he : ∃ i, v i>0:=by
    by_contra! hk
    have ht (i) : v i=0:= Nat.eq_zero_of_le_zero (hk i)
    unfold deg at h; simp [ht] at h
  obtain ⟨i,hi⟩:=he
  apply hv i
  ext j; by_cases hj : j=i
  · subst j; rw [hit,Finsupp.single_eq_same]; have ht:= show v i≤1 from ((show v i ≤ deg v from single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)).trans_eq h); omega
  rw [hit,Finsupp.single_eq_of_ne hj]; have ht:v i+v j≤deg v:=by
    calc
       _ = ∑ a ∈ ({i,j}:Finset Axis), v a := by rw [sum_insert (by simpa using Ne.symm hj),sum_singleton]
       _ ≤ _ := sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _=> Nat.zero_le _)
  omega

lemma stemp (A : Spike) (p:Pin) : Jet.rotate p (crowd i j 0 0 A)=crowd i j 0 0 (CM p A):=by rw [plain0, pure_rotation, plain0]
lemma mirrorRank {B : Spike}(hb : IsUnit B) (hv : ∀ r, f r*f r=1) (hm : ∀ r, MColor r B= f r • B) (l : List Axis) (hl : ∀ i:Axis,i∈l) {X : Pol} (he : X∈channel i j 6): ∃ c : ℂ, travel f l X=c • crowd i j 0 0 B:=by
  refine Submodule.span_induction (p:=fun X _=> ∃ c : ℂ, travel f l X=c • crowd i j 0 0 B) ?_ ?_ ?_ ?_ he
  · rintro v ⟨u,t,a,b,h,rfl⟩; unfold load at h; have ha:=firstR a (by omega); have hb':=firstR b (by omega); subst a; subst b
    rw [← entryMetric]; apply survivor f i j 0 0 (g:=fun _=>1) hb (by simp) hv ?_ ?_ l hl
    · intro A r; rw [stemp]; exact (one_smul ..).symm
    intro r; rw [hm,mul_one]
  · exact ⟨0,by simp⟩
  · rintro x y _ _ ⟨a,ha⟩ ⟨b,hb⟩; exact ⟨a+b,by rw [map_add,ha,hb,add_smul]⟩
  rintro c x _ ⟨a,ha⟩; exact ⟨c*a,by rw [map_smul,ha,mul_smul]⟩
end YM.TorusPCAC.Jet.Selector

#print axioms YM.TorusPCAC.Jet.Selector.mirrorRank
