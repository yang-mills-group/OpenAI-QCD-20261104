import YM.QCD.Revolve.Reef

/-! # both floors turn together -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Revolve
open Lat Lattice Function Finset Wilson Kit
open Pine Flume RG Laurent Bloch YM.Next.Free
open scoped Matrix Matrix.Norms.L2Operator BigOperators
variable {n c f : Side} {j k : ℕ} (F : Flight j k) (hf : f.val=c.val*F.L.val)
variable {s : Signed} {b t t' : Site c} {l : Site f→ℂ} {P : Spike} (h : Glare s ((sliceL F hf).embed t) ((sliceL F hf).embed t') ((sliceL F hf).embed b) l) (hp : Swing s P)

lemma root_affine (r : Ratio c f) (b : Site c) (x : Site c) (s : Signed): shiftE s (r.embed b) (r.embed x)=r.embed (shiftE s b x):=by change affine s (r.embed b) (r.embed x)=_; rw [affine,← r.signed]; exact (r.root.map_add ..).symm
lemma dream (r : Ratio c f) (s : Signed) (b : Site c) (l P): scoop r*hues (r.embed b) s l P=hues b s (l∘r.embed) P*scoop r:=by
  ext i j; let x:=shiftE s b i.1; by_cases he : r.embed x=j.1
  · rw [shows,hues,rr,mouth,root_affine,if_pos he, shown r _ _ (x,j.2) j (Prod.ext he.symm rfl),hues,rr,if_pos rfl]; rfl
  rw [shows,hues,rr,mouth,root_affine,if_neg he,Matrix.mul_apply]; symm; apply sum_eq_zero; intro k _; rw [hues,rr]; split
  next h => rw [scoop,Matrix.of_apply,if_neg,mul_zero]; exact fun H=>he (congr_arg r.embed h|>.trans (congr_arg Prod.fst H))
  rw [zero_mul]

lemma dye_via (K) (x : Cover) (h : x ∈ box K) (s : Signed) : s.act x∈ box K:= by rw [← box_covariant K s]; exact mem_image.mpr ⟨x,h,rfl⟩
def dye (K) (s : Signed): Equiv.Perm ↥(box K):= ⟨fun i=>⟨s.act i.val,dye_via _ _ i.property _⟩,fun i=>⟨s⁻¹.act i.val,dye_via _ _ i.property _⟩,fun i=>Subtype.ext (s.inv_act _),fun i=>Subtype.ext (s.act_inv _)⟩
def starry (P : Patch) (s : Signed): Equiv.Perm P.Points:=dye _ s
lemma alternate (P : Patch) (s : Signed) (x : P.Points): P.weight (starry P s x)=P.weight x:=by
  let K : Equiv.Perm P.Rolls:=Equiv.arrowCongr (Equiv.refl _) (dye _ s)
  have he (i : P.Rolls) : P.addRoll (K i)=starry P s (P.addRoll i):=by apply Subtype.ext; exact (map_sum s.actEquiv (fun j:Fin P.J=>(i j).val) Finset.univ).symm -- check parse
  unfold Patch.weight; rw [← Equiv.sum_comp K]; simp_rw [he,(starry P s).injective.eq_iff]
include h hp
lemma dual (U : Grid f):
    let r:=sliceL F hf
    let V:=pull s (r.embed b) U
    tied F hf (r.embed t) V = hues b s (l∘r.embed) P*tied F hf (r.embed t') U*star (hues (r.embed b) s l P):=by
  intro r V
  let S:=hues b s (l∘r.embed) P; let T:=hues (r.embed b) s l P
  have he (o : Lattice.Order) : lineF F hf (r.embed t) V o=S*lineF F hf (r.embed t') U (orderEquiv s o)*star T := by
    unfold lineF; rw [Matrix.mul_sum,Matrix.sum_mul, ← Equiv.sum_comp (starry F.patch s) (fun i=> S*((F.patch.weight i:ℂ) • (scoop r*routeM (r.embed t') U (route 0 i.val (orderEquiv s o))))*star T)]; refine sum_congr rfl fun i _=>?_
    rw [alternate, Matrix.mul_smul,Matrix.smul_mul]; congr 1; change scoop r*routeM _ (pull _ _ _) _=_; rw [route_shift h hp,aura, ← Matrix.mul_assoc, ← Matrix.mul_assoc]; rw [dream,Matrix.mul_assoc (hues b s (l ∘ r.embed) P)]; rfl
  unfold tied; simp only [Matrix.mul_smul,Matrix.smul_mul]; congr 2; simp only [Matrix.mul_sum,Matrix.sum_mul,he]; exact Equiv.sum_comp (orderEquiv s) (fun i => S*lineF F hf (r.embed t') U i*star T)
lemma spin_vault (U : Grid f) (K : Plan j):
    let r := sliceL F hf
    vaultF K F hf (r.embed t) (pull s (r.embed b) U)= aura (hues (r.embed b) s l P) (vaultF K F hf (r.embed t') U):=by
  intro r
  have ht:=colour_wheel (shrouds r h) hp
  unfold vaultF; rw [aura_add]; congr 1
  · exact spin_wood h hp F.wing K U
  rw [dual F hf h hp U]; -- placeholders
  · unfold aura; simp only [Matrix.conjTranspose_mul, ← Matrix.star_eq_conjTranspose (_:Sheet c),← Matrix.star_eq_conjTranspose (star _),star_star, Matrix.mul_assoc]; rw [← Matrix.mul_assoc (star _) _ _, ht.1, Matrix.one_mul]
end YM.QCD.Revolve
