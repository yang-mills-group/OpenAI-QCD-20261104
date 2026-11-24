import YM.TorusPCAC.Jet.Pairs

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Flavor isolation
Use actual `U(1)^6`, elementary finite selectors here (and if using on a quotient,
carry via intertwining, *not* on an assumed already on-shell basis).
-/
set_option autoImplicit false
noncomputable section
namespace YM.TorusPCAC.Jet
open QCD QCD.Lat Finset Function MeasureTheory TensorProduct Set
open scoped Matrix Topology BigOperators Kronecker TensorProduct Matrix.Norms.Frobenius

namespace Selector
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
def average (a : ℂ) (M : V→ₗ[ℂ] V) : V→ₗ[ℂ] V := (2:ℂ)⁻¹ • (a • M + LinearMap.id)
lemma half (a : ℂ) (M : V→ₗ[ℂ] V) (x : V) : average a M x=(2:ℂ)⁻¹ • (a • M x+x):=rfl
lemma stays (a b : ℂ) (h : a*b=1) {M : V→ₗ[ℂ] V} {x:V} (he:M x=b • x): average a M x=x:=by rw [half,he,smul_smul,h,one_smul, ← two_smul ℂ, inv_smul_smul₀ (by norm_num)]
lemma sinks (a b : ℂ) (h : a*b=-1) {M : V→ₗ[ℂ] V} {x:V} (he:M x=b • x): average a M x=0:=by rw [half,he,smul_smul,h,neg_one_smul,neg_add_cancel,smul_zero]

variable (i j : Flav)
def atFlavor (i : Flav) (u : Circle) : FlavorGroup:=fun j=>if j=i then u else 1
private abbrev I := Complex.I
def twist : Circle:=⟨Complex.I,mem_sphere_zero_iff_norm.mpr Complex.norm_I⟩
@[simp] lemma twist_value : (twist:ℂ)=I:=rfl -- private in exported?

def negatives (i : Flav): Pol→ₗ[ℂ] Pol := average (-1) (flavor (atFlavor i (-1))).toLinearMap
def chirp (i : Flav) (s : Bool) := average (if s then -I else I) (flavor (atFlavor i twist)).toLinearMap
/-- Keep col at j (chirp factor -i), row at i (chirp factor i). -/
def flavorMask := (chirp i false).comp ((chirp j true).comp ((negatives i).comp (negatives j)))
lemma one_leaf (X : Index) (s : Finset Letter) (hn : ∀ v∈s, v.flavor≠i) : flavor (atFlavor i (-1)) (monomial (X,s))=monomial (X,s):= by
  obtain ⟨f,-,he,h⟩:=blades s X
  have hg (p : Fin s.card): flavor (atFlavor i (-1)) (slot (f p))=slot (f p):=by rw [phase]; have e:=hn (f p) ((he _).mpr ⟨p,rfl⟩); unfold axialPhase; split <;> simp [atFlavor,e]
  rw [h,map_mul, map_list_prod,List.map_ofFn]; simp_rw [Function.comp_def,hg]; simp [atPol,flavor]
lemma negatives_dead (X : Index) (s : Finset Letter) (hn : ∀ v∈s, v.flavor≠i) : negatives i (monomial (X,s))=0:= by rw [negatives]; exact sinks _ 1 (by norm_num) (by rw [AlgHom.toLinearMap_apply,one_leaf i _ _ hn,one_smul])
lemma negatives_float (X : Index) (s : Finset Letter) : ∃ z : ℂ, negatives i (monomial (X,s))=z • monomial (X,s) := by
  obtain ⟨f,-,he,h⟩:=blades s X
  have hp (u : FlavorGroup) (s : List Letter) : ∃ z : ℂ, flavor u (s.map slot).prod=z • (s.map slot).prod:=by
    induction s with
    | nil=> exact ⟨1,by simp⟩
    | cons a s ih=> obtain ⟨z,h⟩:=ih; refine ⟨axialPhase u a*z,?_⟩; simp only [List.map_cons,List.prod_cons,map_mul,h,phase,smul_mul_smul_comm]
  have hu : ∃ z : ℂ, flavor (atFlavor i (-1)) (monomial (X,s))=z • monomial (X,s):=by
    obtain ⟨z,hz⟩:= hp (atFlavor i (-1)) (List.ofFn f); simp only [List.map_ofFn,Function.comp_def] at hz; refine ⟨z,?_⟩; rw [h,map_mul,hz,mul_smul_comm]; congr 2; simp [atPol,flavor]
  obtain ⟨z,hz⟩:=hu; rw [negatives]; refine ⟨(2:ℂ)⁻¹*((-1)*z+1),?_⟩; rw [half,AlgHom.toLinearMap_apply,hz]; simp_rw [mul_smul,add_smul,mul_smul,one_smul]

-- small sector (weight through-four)
def sector (d : ℕ) := Submodule.span ℂ {x:Pol| ∃ u v k l a b, load a b ≤ d ∧ x=element i j u v k l a b}
lemma admitted_seed {d : ℕ} (u v k l a b)(h : load a b ≤ d) : element i j u v k l a b ∈ sector i j d := Submodule.subset_span (show ∃ _ _ _ _ _ _, _∧_ from ⟨u,v,k,l,a,b,h,rfl⟩)
lemma little (X : Index) (h:gOrder X≤2) : X=0:=by
  ext i; rw [Finsupp.zero_apply]; by_contra hz
  have he : X i*Labels.generation i≤Labels.height X:=by
    unfold Labels.height; rw [Finsupp.weight_apply,Finsupp.sum]; exact single_le_sum (f:=fun i=> X i • Labels.generation i) (fun _ _=> Nat.zero_le _) (Finsupp.mem_support_iff.mpr hz)
  have hh:= show 2 ≤ X i*Labels.generation i from (show 2 ≤ Labels.generation i from Nat.le_add_left ..).trans (le_mul_of_one_le_left (by omega) (by omega)); unfold gOrder at h; omega

variable {d : ℕ} {x y : Letter}
lemma same_one (hn : i ≠ j) (hx : x.flavor=i) (hy:y.flavor=j) (he:spinOrder x+spinOrder y≤d) : flavorMask i j (slot x*slot y)∈sector i j d:=by
  let X:=slot x*slot y
  have h (z) : flavor z X=(axialPhase z x* axialPhase z y) • X:=by unfold X; rw [map_mul,phase,phase,smul_mul_smul_comm]
  have hv : negatives i X=X:=stays (-1) (-1) (by norm_num) (by rw [AlgHom.toLinearMap_apply,h]; unfold axialPhase; split_ifs <;> simp [hx,hy,atFlavor,Ne.symm hn] <;> exact neg_one_smul ℂ X)
  have hw : negatives j X=X:=stays (-1) (-1) (by norm_num) (by rw [AlgHom.toLinearMap_apply,h]; unfold axialPhase; split_ifs <;> simp [hx,hy,atFlavor,hn] <;> exact neg_one_smul ℂ X)
  change chirp i false (chirp j true (negatives i (negatives j X)))∈_; rw [hw,hv]
  by_cases hh : y.kind=.col
  · have hT : chirp j true X=X:=stays (-I) I (by simp [I]) (by rw [AlgHom.toLinearMap_apply,h]; unfold axialPhase; split_ifs <;> simp_all [atFlavor])
    rw [hT]
    cases ha:x.kind -- names check
    · have hp : chirp i false X=0:=sinks I I (by simp [I]) (by rw [AlgHom.toLinearMap_apply,h]; simp [axialPhase,hh,ha,hx,hy,atFlavor,Ne.symm hn]); rw [hp]; exact Submodule.zero_mem _
    have hp : chirp i false X=X:=stays I (-I) (by simp [I]) (by rw [AlgHom.toLinearMap_apply,h]; simp [axialPhase,hh,ha,hx,hy,atFlavor,Ne.symm hn,I]; exact neg_smul I X); rw [hp]
    have hb : load x.derivatives y.derivatives ≤ d:=by
      rw [load,deg,deg]; apply le_trans _ he; unfold spinOrder; omega
    unfold X; convert admitted_seed i j x.spin y.spin x.color y.color x.derivatives y.derivatives hb using 1
    rcases x with ⟨a,b,c,u,v⟩; rcases y with ⟨f,g,w,t,q⟩; dsimp only at hx hy ha hh; subst b; subst g; subst a; subst f; rfl
  have hT : chirp j true X=0:= sinks (-I) (-I) (by simp [I]) (by rw [AlgHom.toLinearMap_apply,h]; unfold axialPhase; split_ifs <;> simp_all [atFlavor,I] <;> exact neg_smul I X)
  rw [hT,map_zero]; exact Submodule.zero_mem _

lemma sector_mark (hn : i ≠ j) (p : Index) (s : Finset Letter) (hd : d≤8)(he:orders (p,s) ≤ d) : flavorMask i j (monomial (p,s))∈sector i j d:=by
  by_cases H : ∃ x∈s,x.flavor=j
  swap
  · push Not at H
    simp only [flavorMask,LinearMap.comp_apply,negatives_dead j p s H,map_zero,Submodule.zero_mem]
  by_cases H' : ∃ x∈s,x.flavor=i
  swap
  · push Not at H'; obtain ⟨c,hc⟩:=negatives_float j p s
    simp only [flavorMask,LinearMap.comp_apply,hc,map_smul, negatives_dead i p s H',map_zero,smul_zero,Submodule.zero_mem]
  obtain ⟨y,hy,rfl⟩:= H; obtain ⟨x,hx,rfl⟩:= H'; have h:x≠y:=fun e=>hn (congr_arg _ e)
  have hk : s={x,y} :=by
    have hl : s.card*3 ≤ 8:= cap_sites.trans (he.trans hd); have hv : ({x,y}:Finset Letter)⊆s:= by exact Finset.insert_subset hx (Finset.singleton_subset_iff.mpr hy)
    exact (eq_of_subset_of_card_le hv (by rw [Finset.card_pair h]; omega)).symm
  subst s; rw [orders] at he; dsimp only at he; rw [sum_insert (by simpa),sum_singleton] at he;
  have ht:3 ≤ spinOrder x:=by unfold spinOrder; omega
  have hh:3 ≤ spinOrder y:=by unfold spinOrder; omega
  have hv: p=0:=little p (by omega)
  subst p; have hu:= units {x} {y} (by simp [h]) 0 0; simp only [zero_add,Finset.singleton_union,← silicon] at hu
  have hp : flavorMask x.flavor y.flavor (slot x*slot y)∈sector x.flavor y.flavor d:=same_one x.flavor y.flavor hn rfl rfl (by omega)
  rcases hu with ht|ht
  · rw [← ht]; exact hp
  rw [show monomial (0,{x,y})=-(slot x*slot y) from (by rw [ht, neg_neg]),map_neg]; exact Submodule.neg_mem _ hp

lemma supported (hn : i≠j) (v : Pol)(h:v∈cap d)(hd:d≤8) : flavorMask i j v∈ sector i j d :=by
  refine Submodule.span_induction (p:=fun v _=> flavorMask i j v∈sector i j d) ?_ ?_ ?_ ?_ h
  · rintro x ⟨⟨a,b⟩,hx,rfl⟩; exact sector_mark i j hn _ _ hd hx
  · simp
  · intro a b _ _ h h'; rw [map_add]; exact Submodule.add_mem _ h h'
  intro c a _ ha; rw [map_smul]; exact Submodule.smul_mem _ _ ha
end Selector
end YM.TorusPCAC.Jet

#print axioms YM.TorusPCAC.Jet.Selector.supported
