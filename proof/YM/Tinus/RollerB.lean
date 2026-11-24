import YM.Patria.Orchid
import YM.Tinus.Screws
import YM.Massive.PCAC.Echo
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Rolls
open Function Lattice RG Filter Finset
open scoped BigOperators Classical
variable {X:Type} [AddCommGroup X][Module ℝ X]
variable {c f:Side} (g:Ratio c f) (F: Site f→X)
local notation "M"=> g.count
local notation "S"=> Site M
local notation "w"=> wrap f
set_option quotPrecheck false
local notation "ℓ"=> (M).val
local notation "V"=> F∘w
abbrev Stuff (L:Side):= Fin L.val×Fin L.val × Fin L.val × Fin L.val
noncomputable def dustR (c:Side) (k:Fin c.val):ℤ:= k.val - centre c.val
-- caution Nat-? centre :Z ok
noncomputable abbrev draw (c:Side)(i:Stuff c):Cover:= ![dustR c i.1,dustR c i.2.1,dustR c i.2.2.1,dustR c i.2.2.2]
noncomputable abbrev lexus (c:Side)(i:Stuff c): Site c:= wrap c (draw c i)
lemma dusty (h:Odd c.val)(k:Fin c.val): - (c.val:ℤ)< 2*(dustR c k)∧ 2*dustR c k ≤ c.val:=by rcases h with ⟨p,hp⟩; unfold dustR centre; omega
lemma charG (h:Odd c.val)(i:Stuff c) : lift (lexus c i)= draw c i:=by apply lift_eq_iff.mpr; refine ⟨rfl, fun a=>?_⟩; fin_cases a <;> first|exact dusty h i.1|exact dusty h i.2.1|exact dusty h i.2.2.1|exact dusty h i.2.2.2
lemma charJ (h:Odd c.val): Bijective (lexus c):=by
     apply (Fintype.bijective_iff_injective_and_card ..).mpr; refine ⟨fun i j hj=> ?_,?_⟩; · have ht:=congr_arg Lattice.lift hj; rw [charG h,charG h] at ht; have hv(a):=congr_fun ht a; have hI(i j:Fin c.val)(h:dustR c i=dustR c j): i=j:=Fin.ext (Nat.cast_injective (R:=ℤ) (sub_left_injective h)); exact Prod.ext (hI _ _ (hv 0)) (Prod.ext (hI _ _ (hv 1)) (Prod.ext (hI _ _ (hv 2)) (hI _ _ (hv 3))))
     rw [site_card,Fintype.card_prod,Fintype.card_prod,Fintype.card_prod,Fintype.card_fin]; ring
noncomputable def extra (u:Sail)(s:List Axis) := s.flatMap fun i=> List.replicate (u i).val (i,(2:ℕ))
local notation "X0"=> [(0,1),(1,1),(2,1),(3,1)]
local notation "E"=> (Equiv.ofBijective (lexus M))
private lemma past (s:List Axis) (u:Sail) (V':Cover→ X) (m:ℕ): rolls 1 m (s.flatMap (lanes u)) V' = rolls 1 m (s.map fun x=> (x,1)) (rolls 1 m (extra u s) V'):=by
     induction s with| nil=> rfl | cons a s ih=>
        unfold lanes; simp only [List.map_cons, extra,List.flatMap_cons,List.cons_append,rolls,append]; congr 1; unfold lanes at ih; rw [ih]; apply roll_move -- check
private lemma secondary (V':Cover→X)(k:Cover): rolls 1 (M).val X0 V' k = (((M).val:ℝ)^4)⁻¹ • (∑ j:Stuff M,V' (k + draw M j)):=by
     simp_rw [rolls,sumG]; simp_rw [← Finset.smul_sum,smul_smul]; rw [← inv_pow]; congr 1; · ring
     simp_rw [Fintype.sum_prod_type]; refine sum_congr rfl fun i _=>sum_congr rfl fun j _=>sum_congr rfl fun u _=>sum_congr rfl fun v _=>?_; refine congr_arg V' ?_; funext a; rw [add_assoc,add_assoc,add_assoc]; unfold stride; simp [dustR,draw,Pi.add_apply]; -- try fin_cases
     fin_cases a<;> simp [step_apply,dustR]
lemma harmony (h:Odd ℓ) : ∑ k:Site c,rolls 1 (M).val X0 V (ℓ • lift k)= (((M).val:ℝ)^4)⁻¹ • (∑ i:Site f,F i):=by
     let G:= E (charJ h); let p:=g.splitSites
     have he(k:Site c): rolls 1 ℓ X0 V (ℓ • lift k)= ((ℓ:ℝ)^4)⁻¹ • ∑ j:S,F (g.assemble (k,j)):=by
          rw [secondary _ _,← G.sum_comp]; apply congr_arg; refine sum_congr rfl fun i _=> congr_arg F ?_; change w (ℓ • lift k+ draw M i)= g.embed _+ _; rw [map_add, show lift (G i)=_ from charG h i]; rfl
     simp_rw [he]; rw [←smul_sum]; apply congr_arg; rw [← Fintype.sum_prod_type']; -- orientation simp via p
     exact p.symm.sum_comp F
lemma harmonyR (h:Odd ℓ)(u:Sail) : ∑ k:Site c, Averaging.filter (.some u) ℓ V (ℓ • lift k)= (((M).val:ℝ)^4)⁻¹ • (∑ i:Site f,F i):=by
      have hg:List.finRange 4=[0,1,2,3]:=by decide
      let j:= extra u (List.finRange 4); have hw:∀ s:List PairS,∃ Z:Site f→X,rolls 1 ℓ s V= Z ∘ w ∧ ∑ i:Site f, Z i=∑ i:Site f,F i:=by
           intro s; induction s with| nil=>exact ⟨F,rfl,rfl⟩| cons a l ih=>
               obtain ⟨Z,hZ,hP⟩:=ih; let L:=fun v:Fin ℓ=> Equiv.addRight (w (stride a 1 v)); refine ⟨fun i=> (ℓ:ℝ)⁻¹ • ∑ j:Fin ℓ, Z (L j i),?_,?_⟩
               · funext b; rw [rolls,hZ,sumG]; exact congr_arg ((ℓ:ℝ)⁻¹ • ·) (sum_congr rfl (fun i _=> congr_arg Z (map_add ..)))
               rw [← smul_sum, sum_comm]; simp_rw [fun (j: Fin ℓ)=> Equiv.sum_comp (L j) Z,hP]; rw [sum_const,card_univ,Fintype.card_fin,← Nat.cast_smul_eq_nsmul ℝ, inv_smul_smul₀ (by positivity : (ℓ:ℝ)≠0)]
      obtain ⟨Z,hZ,hP⟩:= hw j; unfold j at hZ; simp_rw [roles,menu,past (s:=(List.finRange 4)), hZ]; rw [hg]; exact (harmony g Z h).trans (congr_arg _ hP)
end YM.Massive.Patria.Rolls
#print axioms YM.Massive.Patria.Rolls.harmonyR
