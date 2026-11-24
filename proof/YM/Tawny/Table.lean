import YM.Tawny.Party
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tawny
open QCD QCD.Lat QCD.Grass Lattice TensorProduct Function UV PCAC
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator ContDiff Classical TensorProduct
variable {d:ℕ}(a b:Flavor 6)
open Poised.Display Poised.Stative Module Finset Oriole Pane TensorProduct Revolve UV.Free KeysP BendR Clifford
namespace Cast
open StressFlux.Offer (acts marks Vc)
open Rays
namespace TableT
open scoped Kronecker
open Zinc Carnal Perla
local notation "D"=>10
local notation "P"=> Multi D
local notation "U"=> (0:P)
local notation "L"=>leadR
local notation "H"=>ηR
variable (i j k:Axis) (S:Spike)
-- Delta meters for prism0 and prism1
variable (p q p' q': Multi d)
lemma bareB : prism0 a p q (bilinear b b S p' q')= if a=b ∧ p=p'∧q=q' then S else 0:=by
   rw[← j_stard,probed]; unfold silver; rw [show skin 0 (jcoat _) = fieldB b b p' q' (wave S) from j_coat _]; change ingot (Oriole.prism a a p q _) = _
   have he: Oriole.prism a a p q (fieldB b b p' q' (wave S))=if a=b∧p=p'∧q=q' then wave S else 0:=by
        ext i j; change fieldB _ _ _ _ _ ((p,i),a) ((q,j),a)=_; rw[fieldK]; simp only; by_cases h:a=b∧p=p'∧q=q'; · rw [if_pos h, if_pos (by tauto)]
        rw[if_neg h, if_neg (by tauto)]; rfl -- diag.
   rw [he]; split; exact Stew.leafy _; exact map_zero _
lemma bareC : prism1 a p q i j (bilinear b b S p' q')=0:=by unfold prism1; rw[LinearMap.comp_apply,LinearMap.comp_apply,← j_stard,ray,LinearMap.sub_apply]; change gold2 (gravel a a p q (skin _ ((1:GPol)⊗ₜ[ℂ] coat _)- skin _ ((1:GPol)⊗ₜ[ℂ] coat _)))=_; rw [mintSkin,mintSkin,map_one,map_one,sub_self,map_zero,map_zero]
lemma bareFog:fog (bilinear a a S p q)=0:=by rw[← j_stard]; exact mintFog ..
lemma clear_P(x:GPol):prism0 a p q (plain d x)=0:=by rw[prism0,LinearMap.comp_apply,LinearMap.comp_apply,plainP,unit_skin,map_zero,map_zero]
lemma clear_K(x:GPol):prism1 a p q i j (plain d x)=0:=by unfold prism1; rw[LinearMap.comp_apply,LinearMap.comp_apply,ray,LinearMap.sub_apply,plainP,unit_skin,unit_skin,sub_zero,map_zero,map_zero]
variable (l:Axis)
lemma measure_Y : prism1 a U U i j (youthL b k l S)=if a=b then (((↑(basis i k*basis j l-basis i l*basis j k):ℂ))) • S else 0:=by
   unfold prism1; rw [LinearMap.comp_apply,LinearMap.comp_apply,ray,LinearMap.sub_apply,skinP,skinP0,sub_zero,Pi.single_eq_same]; unfold weave; change gold2 (Oriole.prism _ _ _ _ _)=_; rw[yield_p]; by_cases h:a=b
   · subst b; simp only[↓reduceIte,and_true]; unfold whirl; rw [StressFlux.curl0_leg] -- orientation leg i j x,y? lemma basis k i...
     let r:= basis i k*basis j l - basis i l*basis j k; let g:su.Color:= Gpick
     rw [show basis k i=basis i k from by simp [eq_comm],show basis l j=basis j l from by simp [eq_comm],show basis k j=basis j k from by simp [eq_comm],show basis l i=basis i l from by simp[eq_comm],mul_comm (basis j k), show BendR.ore (r • g)=(↑r:ℂ) • BendR.ore g from su.colorMat.map_smul r g, Matrix.kronecker_smul, map_smul, gilt2]
   simp [h]
lemma measure_L : prism0 a U U (youthL b i j S)=0:=by unfold prism0; rw [LinearMap.comp_apply,LinearMap.comp_apply,skinP0,map_zero,map_zero]
lemma hic : L i≠U:=by intro h; have he:= gradeL i; rw [h,gradeV] at he; contradiction
lemma hit : H i j≠U:=by intro h; have he:= gradeH i j; rw [h,gradeV] at he; contradiction
lemma tip : L i = L j ↔ i=j:=lead_in.eq_iff
lemma tap : L i ≠ H j k:=by intro h; have he:=gradeL i; rw[h,gradeH] at he; contradiction
lemma lotJ {i j k l:Axis} : H i j = H k l ↔ i=k∧j=l ∨ i=l∧j=k:=by
    constructor; exact H_unique i j k l; rintro (⟨rfl,rfl⟩|⟨rfl,rfl⟩); rfl; exact H_swap ..
lemma print_p : H i j=H i k ↔ j=k:=by rw[lotJ]; constructor; rintro (⟨_,h⟩|⟨h,h'⟩); exact h; exact h'.trans h; exact fun h=> Or.inl ⟨rfl,h⟩
lemma print_r : H i k=H j j ↔ i=j ∧ k=j :=by rw[lotJ,or_self]
-- Values convenience
variable (f:Flavor 6)
local notation "V"=> RawVec 10
lemma sea_val : (beeA f).val i =∑ j:Axis,sea f i j:=rfl
lemma bee_val : (bee f).val i=beta f i:=rfl
lemma lup_val:(lup f).val i=shell0 f i i:=rfl
lemma lap_val:(lapL f).val i=∑ j:Axis,shell0 f i j:=rfl
lemma s_val:(slashS f).val i=∑ j:Axis,shell1 f i j:=rfl
lemma t_val:(slashT f).val i=∑ j:Axis,shell2 f i j:=rfl
lemma star_val:(starV f).val i=∑ j:Axis,med f i j (gamma j):=rfl
end TableT
end Cast
end YM.Massive.Tawny
#print axioms YM.Massive.Tawny.Cast.TableT.measure_Y
