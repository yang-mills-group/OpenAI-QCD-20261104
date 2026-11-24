import YM.Massive.Pressure.Pivots

/-!
# Triangular integration

Two uses: numerator cost with all pivots, denominator cost with the
independent gauge-rotation degrees at all sites smoothing a read at a point.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Pressure.Triangle
open Lattice RG Wilson Function SectorNext.Vacuum SectorNext.Vacuum.Masts Filter MeasureTheory Finset
open scoped Matrix.Norms.Frobenius BigOperators Topology Classical
variable {n : Side} (G : Gauge) {ι ν : Type*} [Fintype ι]

def kick (i : ι) (u : G.El) (X : ι→G.El) := update X i (u*X i)

omit [Fintype ι] in
@[simp] lemma kick_at (i : ι) (u : G.El) (X : ι→G.El) : kick G i u X i=u*X i:= update_self ..
omit [Fintype ι] in
lemma kick_off (i : ι) (u : G.El) (X : ι→G.El) {j : ι} (he : j ≠ i) : kick G i u X j=X j:= update_of_ne he ..

omit [Fintype ι] in
@[fun_prop] lemma kick_joint (i : ι) : Continuous (fun p:G.El × (ι→G.El) => kick G i p.1 p.2):=by
  apply continuous_pi; intro j; by_cases h : j=i
  · subst j; simp; fun_prop
  simp_rw [kick_off _ _ _ _ h]; fun_prop

omit [Fintype ι] in
lemma kick_mul (i : ι) (u : G.El) : kick G i u = fun X : ι→G.El => (Pi.mulSingle i u) * X:=by
  funext X j; by_cases h:i=j; subst j; simp
  simp [kick_off _ _ _ _ (Ne.symm h),Ne.symm h]

abbrev law (G : Gauge) (ι : Type*) [Fintype ι] : Measure (ι→G.El) := Measure.pi fun _ : ι=> G.probHaar

lemma peel (F : (ι→G.El)→ℝ) (i : ι) (hf : Continuous F) :
    (∫ U,F U ∂law G ι) = ∫ U,(∫ u,F (kick G i u U) ∂G.probHaar) ∂law G ι:=by
  have hh : Integrable (Function.uncurry (fun u X => F (kick G i u X))) (G.probHaar.prod (law G ι)):= (hf.comp (kick_joint G i)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [← integral_integral_swap hh]; have he (u : G.El) : (∫ X, F (kick G i u X) ∂ law G ι)=∫ X, F X ∂ law G ι := by
    rw [kick_mul]; let t : ι → G.El := Pi.mulSingle i u
    have hp : MeasurePreserving (fun p:ι→G.El=>t*p) (law G ι) (law G ι) := measurePreserving_pi _ _ (fun j=> measurePreserving_mul_left G.probHaar (t j))
    exact hp.integral_comp (Homeomorph.mulLeft t).measurableEmbedding F
  simp_rw [he]; simp

-- priority linearly ordered; ties are mutually independent.
variable {B : Type*} [LinearOrder B] (price : ν→B) (F : ν → (ι→G.El) → ℝ)
theorem triangle (X : Finset ν) (p : ν→ι) (y : ℝ) (hf : ∀ i, Continuous (F i))
    (hX : ∀ i U, (∫ u, F i (kick G (p i) u U) ∂G.probHaar)=y)
    (hp : ∀ i j, i≠j → price j ≤ price i → ∀ u U, F j (kick G (p i) u U) = F j U) :
    (∫ U,(∏ i ∈ X, F i U) ∂law G ι) = y^X.card:=by
  classical
  induction X using Finset.strongInduction with
  | H X ih =>
    by_cases hu : X.Nonempty
    swap; · rw [not_nonempty_iff_eq_empty.mp hu]; simp
    obtain ⟨i,hi,h⟩:= exists_max_image X price hu
    let t := X.erase i; let f (U : ι→G.El) := ∏ j∈t, F j U
    have hk U : ∏ j ∈ X, F j U= F i U*f U:=Eq.symm (mul_prod_erase X (fun j=> F j U) hi) -- check
    have he U u : f (kick G (p i) u U)= f U := prod_congr rfl (fun j hj=>hp i j (Ne.symm (mem_erase.mp hj).1) (h j (mem_erase.mp hj).2) u U)
    have hm : Continuous f:= continuous_finsetProd _ fun j _=>hf j
    simp_rw [hk]; rw [peel G (fun U=>F i U * f U) (p i) ((hf i).mul hm)]; simp_rw [he,integral_mul_const,hX]
    rw [integral_const_mul,show (∫ U,f U ∂law G ι)=_ from ih t (erase_ssubset hi)]
    rw [show X.card=t.card+1 from (card_erase_add_one hi).symm] -- motive? rewrites elsewhere?
    exact (pow_succ' ..).symm

section link
variable (f : G.El→ℝ)
omit [Fintype ι] in
lemma wrap_price (e h : G.El) :
    (∫ u,f (e*u*h) ∂G.probHaar)=∫ u,f u ∂G.probHaar:=by
  calc
    _ = ∫ u,f (u*h) ∂G.probHaar := (measurePreserving_mul_left G.probHaar _).integral_comp (Homeomorph.mulLeft e).measurableEmbedding (fun u=> f (u*h))
    _ = _ := (measurePreserving_mul_right G.probHaar _).integral_comp (Homeomorph.mulRight h).measurableEmbedding _
lemma wrap_inverse (e h : G.El) :
    (∫ u, f (e*u⁻¹*h) ∂ G.probHaar)=∫ u,f u ∂G.probHaar:=by
  calc
    _ = ∫ u,f (e*u*h) ∂ G.probHaar := (Measure.measurePreserving_inv G.probHaar).integral_comp (Homeomorph.inv G.El).measurableEmbedding (fun u=> f (e*u*h))
    _ = _ := wrap_price G f ..

lemma face_edge (X : Config G n) (y : Site n) (a b : Axis) (h : a<b) :
    faceValue X (y,⟨(a,b),h⟩)= X (y,a) * (X (y+step a,b) * ((X (y+step b,a))⁻¹ * (X (y,b))⁻¹)):=by
  simp only [faceValue,Lattice.square,travel,Step.pos_read,Step.neg_read,Step.vec_pos,Step.vec_neg,mul_one]; congr 4 <;> abel_nf

lemma depends_edges (X : Config G n) (t : Face (Per n)) (e : Link n) (he : e∉edges t) (u) :
    faceValue (kick G e u X) t=faceValue X t:=by
  rcases t with ⟨y,a,h⟩; rcases a with ⟨a,b⟩
  obtain ⟨h1,h2,h3,h4⟩:(y,a)≠e∧(y+step a,b)≠e∧(y+step b,a)≠e∧(y,b)≠e:=by simpa [edges,eq_comm (a:=e)] using he
  rw [face_edge,face_edge]; simp only [kick_off G _ _ _ h1,kick_off G _ _ _ h2,kick_off G _ _ _ h3,kick_off G _ _ _ h4]

lemma plane_price (hn : 1<n.val) (t : Face (Per n)) (U : Config G n) (e : Link n) (h : e∈edges t):
    (∫ u, f (faceValue (kick G e u U) t) ∂ G.probHaar)=∫ u,f u ∂G.probHaar:=by
  classical
  have hx (x : Site n) (a : Axis) : x+step a≠x:=by
    haveI : Fact (1<n.val):=⟨hn⟩; intro hp
    have he:=congr_fun hp a; simp at he
  rcases t with ⟨y,⟨⟨a,b⟩,he⟩⟩
  have ha:a≠b:=he.ne
  let i:= (y,a); let j:= (y+step a,b); let k:= (y+step b,a); let l:= (y,b)
  have h1 : i ≠ j:=fun hh=>ha (congr_arg Prod.snd hh)
  have h2 : i ≠ k:=fun hh=>hx _ _ (congr_arg Prod.fst hh.symm)
  have h3 : i ≠ l:=fun hh=>ha (congr_arg Prod.snd hh)
  have h4 : j ≠ k:=fun hh=>ha (congr_arg Prod.snd hh.symm)
  have h5 : j ≠ l:=fun hh=>hx _ _ (congr_arg Prod.fst hh)
  have h6 : k ≠ l:=fun hh=>ha (congr_arg Prod.snd hh)
  simp_rw [face_edge]
  let Y u := kick G e u U
  change (∫ u,f (Y u i*(Y u j *((Y u k)⁻¹*(Y u l)⁻¹))) ∂G.probHaar)=_
  unfold Y; change e ∈ {i,j,k,l} at h; simp only [mem_insert,mem_singleton] at h
  rcases h with rfl|rfl|rfl|rfl
  · simp_rw [kick_at,kick_off _ _ _ _ h1.symm, kick_off _ _ _ _ h2.symm,kick_off _ _ _ _ h3.symm,mul_assoc]
    simpa only [one_mul] using wrap_price G f 1 (U i*(U j*((U k)⁻¹*(U l)⁻¹)))
  · simp_rw [kick_at,kick_off _ _ _ _ h1,kick_off _ _ _ _ h4.symm,kick_off _ _ _ _ h5.symm,mul_assoc]
    simpa only [mul_assoc] using wrap_price G f (U i) (U j * ((U k)⁻¹ * (U l)⁻¹))
  · simp_rw [kick_at,kick_off _ _ _ _ h2,kick_off _ _ _ _ h4,kick_off _ _ _ _ h6.symm,mul_inv_rev,mul_assoc]
    simpa only [mul_assoc] using wrap_inverse G f (U i * U j * (U k)⁻¹) ((U l)⁻¹)
  simp_rw [kick_at,kick_off _ _ _ _ h3,kick_off _ _ _ _ h5,kick_off _ _ _ _ h6,mul_inv_rev];
  simpa only [mul_assoc,mul_one] using wrap_inverse G f (U i * U j * (U k)⁻¹ * (U l)⁻¹) 1

/-- Works also with no gauge fixing in the end. Retains the Wilson-power estimate
(population payment with exponent `3*(#sites-1)`). Need n>1. -/
lemma triangular (X : Finset (Tor n)) (hn : 1<n.val) (h : Continuous f) :
    (∫ U,(∏ i∈X,f (faceValue U (lens i))) ∂prior G n)=(∫ u,f u ∂ G.probHaar)^X.card:=by
  apply triangle G (fun i=>ranking i.val) (p:=fun i=>i.val) (fun i U=>f (faceValue U (lens i))) X
    (∫ u,f u ∂ G.probHaar) (fun i=>by unfold faceValue; fun_prop) (fun i U=>plane_price G f hn _ _ _ (lens_has i))
  intro i j he hp u U; apply congr_arg f; apply depends_edges
  intro hx; rcases no_later j hn _ hx with hh|hh
  · exact he (Subtype.ext hh)
  exact (hh i.property).not_ge hp
end link
end YM.Massive.Pressure.Triangle
#print axioms YM.Massive.Pressure.Triangle.triangular
