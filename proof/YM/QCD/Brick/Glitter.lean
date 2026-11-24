import YM.QCD.Brick.Wand
/-! # sum Rank two ticket; pay max(Der) weighted once -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Brick
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
open Garden Fork Leaf Tee Flume YM.Next.Free Laurent
variable {c f : Side} {N n:ℕ} {p v r A:ℝ}
variable (o:Site f)
local notation "L"=> Modes f N
def nimb (s:Finset (Keys f N)):ℕ:= (s.sup (Stew.lens o))
lemma trail_size (x: Site f):size (heel o x) ≤4*separation x o:=by
    unfold Laurent.size; refine (sum_le_sum (g:=fun _ : Axis=> separation x o) fun i _=> ?_).trans_eq ?_
    · exact component_le ..
    rw [sum_const,card_univ]; simp [Axis]
lemma altitude (i j:Note N)(x y:Site f): let s:=tag (placeQ x i) (placeQ y j); size (heel o x) ≤ 4*nimb o s ∧ size (heel o y)≤4*nimb o s ∧ (1+(4*nimb o s:ℕ))^2 ≤ 16*pieD (Stew.lens o) s:=by
   intro s; have hx: separation x o ≤ nimb o s:= le_sup (f:=Stew.lens o) (show Sum.inr (placeQ x i)∈ s by simp [s,tag]); have hy : separation y o≤nimb o s:= le_sup (f:=Stew.lens o) (show Sum.inl (placeQ y j)∈s by simp [s,tag]); refine ⟨(trail_size o x).trans (Nat.mul_le_mul_left 4 hx), (trail_size o y).trans (Nat.mul_le_mul_left 4 hy),?_⟩; unfold pieD; change _ ≤ 16*(1+nimb o s)^2; nlinarith
variable {b:Bool}
lemma dreams (M: FormN f N)(F:Kit.Rail f c)(h:lights o b M) : apple F N (form M)=∑ i:Note N, ∑ j:Note N, ∑ x: Site f,∑ y:Site f, signN o M i j x y • (staff o F (Sum.inl j) (heel o y)*staff o F (Sum.inr i) (heel o x)-dazzle b (staff o F (Sum.inl j)) (staff o F (Sum.inr i)) (heel o y) (heel o x)):=by
   rw [born o]; refine sum_congr rfl fun i _=> sum_congr rfl (fun j _=>?_); simp_rw [smul_sub,sum_sub_distrib, friend o _ _ _ _ b M h, sub_zero]
def tips (p:Bool)(v:ℝ):ℝ:= if p then v^2 else v
variable {F: Kit.Rail f c}{w: Keys c N→ℕ}
lemma river (M: FormN f N)(h:lights o b M)(hQ:∀ q:Accent N,Lien w v r A (staff o F q)) (hx:0<r)(hv:0≤v)(hV:v≤1)(hA:0≤A): visc w r (apple F N (form M))≤ 16*(340*A^2*tips b v)*(∑ i:L,∑ j:L, ‖M i j‖*(pieD (Stew.lens o) (tag i j):ℝ)):=by
    rw [dreams o _ _ h]; apply (vc_sum ..).trans; let C:= 16*(340*A^2*tips b v)
    conv_rhs=> rw [mode_sum (f:=f) (N:=N) (fun i: L=>∑ j,_*(pieD (Stew.lens o) (tag i j):ℝ))]
    simp_rw [mode_sum] -- edit
    rw [Finset.mul_sum]; apply sum_le_sum; intro i hi; apply (vc_sum ..).trans; rw [sum_comm (f:=fun x:Site f=>fun j:Note N=>∑ y:Site f, ‖M (placeQ x i) (placeQ y j)‖*(pieD (Stew.lens o) (tag _ _):ℝ)), Finset.mul_sum]; apply sum_le_sum; intro j hj; apply (vc_sum ..).trans; rw [Finset.mul_sum]; apply sum_le_sum; intro x hx'; apply (vc_sum ..).trans; rw [Finset.mul_sum]; apply sum_le_sum; intro y hy
    let P:=tag (placeQ x i) (placeQ y j); let d:=4*nimb o P
    obtain ⟨h1,h2,h3⟩:= altitude o i j x y
    have hz: (1+(d:ℝ))^2 ≤ 16*pieD (Stew.lens o) P:=by exact_mod_cast h3
    rw [vc_scale]; unfold signN; rw [norm_mul,norm_mul, show ‖shine o x‖=1 by rcases shines o x with H|H <;>simp [H],show ‖shine o y‖=1 by rcases shines o y with H|H<;>simp [H],one_mul,one_mul]; have hm := pollinate (hQ (Sum.inl j)) (hQ (Sum.inr i)) h2 h1 hx hv hV hA
    have hh : visc w r (staff o F (Sum.inl j) (heel o y) * staff o F (Sum.inr i) (heel o x) - dazzle b (staff o F (Sum.inl j)) (staff o F (Sum.inr i)) (heel o y) (heel o x)) ≤ 340*A^2*tips b v*(1+(d:ℝ))^2:=by
       cases b; exact hm.1; exact hm.2  -- implicit arg
    apply (mul_le_mul_of_nonneg_left hh (norm_nonneg _)).trans; have he:0 ≤340*A^2*tips b v:=mul_nonneg (by positivity) (ite_nonneg (sq_nonneg _) hv)
    apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hz he) (norm_nonneg _)).trans_eq; dsimp only [P]; ring
lemma sumBl (W : Alg (Pairs (Modes f N)))(hp:0≤ r): (∑ i:L,∑ j:L,‖grasp W i j‖ * ↑(pieD (Stew.lens o) (tag i j)))*r^2 ≤ Stew.plank o r W :=by
   let A:=L×L; let g(v:A): Finset (Keys f N):=Stew.tag v.1 v.2; have hg:Injective g:=fun a b h=> Prod.ext ((tagged ..).1 h).1 ((tagged ..).1 h).2
   have h(v:A): ‖grasp W v.1 v.2‖*↑(pieD (Stew.lens o) (g v))*r^2=starch (Stew.lens o) r (g v)*‖coef (g v) W‖:=by
       unfold starch; rw [show (g v).card=2 from (by unfold g tag; simp)]
       have hh : ‖grasp W v.1 v.2‖= ‖coef (g v) W‖:=by unfold grasp; rcases bitS v.1 v.2 with hb|hb<;> simp [hb,g]
       rw [hh]; ring
   rw [← Fintype.sum_prod_type (f:=fun v:A=> ‖grasp W v.1 v.2‖* ↑(pieD (Stew.lens o) (g v))),Finset.sum_mul]; simp_rw [h]; rw [← Finset.sum_image (f:=fun i=>starch (Stew.lens o) r i * ‖coef i W‖) (s:=univ) hg.injOn, Stew.plank,pricesD (Stew.lens o) hp]; exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _=>mul_nonneg (starch_pos _ hp _) (norm_nonneg _))
end YM.QCD.Brick
