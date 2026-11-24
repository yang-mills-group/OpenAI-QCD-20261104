import YM.Tarn.Temple
import YM.Fir.Bound
/-! Full-motion rank union W constructed from numeric limit on Tags. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tarn
open YM.Fir Fir Fir.Gains Fir.TagF Filter Set Metric
open QCD QCD.Lat UV Lattice Poised Plans Plans.Stamp Intag.Vale
open scoped Topology ContDiff BigOperators Classical
variable (Z:SpaceZ) {n:ℕ}
open Function
structure Story where
    n:ℕ
    x:Points n
    t:Fin n→TagF
    p:Fin n
    hx:x∈conf n
abbrev Cargo:= Story→ℂ
noncomputable def zodiac (d:ℕ):Label d→ₗ[ℂ] Cargo:= LinearMap.pi fun v:Story=> puts Z v.x v.t v.p d
noncomputable def foliage :Submodule ℂ Cargo:= ⨆ d:ℕ, LinearMap.range (zodiac Z d)
noncomputable def plume (d:ℕ):Label d→ₗ[ℂ]foliage Z:= (zodiac Z d).codRestrict _ (fun p=> (le_iSup (fun i=> LinearMap.range (zodiac Z i)) d :LinearMap.range (zodiac Z d)≤ foliage Z) (LinearMap.mem_range_self ..))
abbrev Cresc : Prop:=Monotone fun d=>LinearMap.range (zodiac Z d)
noncomputable abbrev signets(t:TagF):= plume Z t.1 t.2
namespace Cresc
variable {Z}(h:Cresc Z)
include h
lemma sealed (x:foliage Z):∃ d,∃ p:Label d, plume Z d p=x :=by
    obtain ⟨d,p,hp⟩:= Submodule.mem_iSup_of_directed _ (Monotone.directed_le h) |>.mp x.property; exact ⟨_,p,Subtype.ext hp⟩
lemma bell(v: foliage Z) :∃ t:TagF,signets Z t=v:=by obtain ⟨d,p,rfl⟩:=h.sealed v; exact ⟨⟨d,p⟩,rfl⟩
lemma growth : Monotone fun d=>LinearMap.range (plume Z d):=by
    rintro i j hij _ ⟨z,rfl⟩; obtain ⟨p,hp⟩:= h hij (LinearMap.mem_range_self (zodiac Z i) z); exact ⟨_, Subtype.ext hp⟩
lemma allure (u v:foliage Z):∃ d,∃ p q:Label d, u=plume Z d p∧ v=plume Z d q:=by
    obtain ⟨i,p,hp⟩:= h.sealed u; obtain ⟨j,q,hq⟩:=h.sealed v; obtain ⟨p,hp'⟩:= h.growth (le_max_left i j) ⟨p,hp⟩; obtain ⟨q,hq'⟩:= h.growth (le_max_right i j) ⟨q,hq⟩; exact ⟨_,p,q,hp'.symm,hq'.symm⟩
end Cresc
namespace Zodiac
variable {Z}{x:Points n}(hx:x∈conf n)
-- story used by S.Legible quotient any tag
include hx
lemma stars(t t':Fin n→TagF)(h:∀ i,signets Z (t i)=signets Z (t' i)):handle Z t x=handle Z t' x:=by
    let F(s:Finset (Fin n))(i:Fin n):=if i∈s then t i else t' i
    have he(s:Finset (Fin n)):handle Z (F s) x=handle Z t' x:=by
        induction s using Finset.induction_on with
        | empty=>rw [show F ∅=t' from by ext1; simp[F]]
        | insert a s ha ih=>
          have hu: F (insert a s)= Function.update (F s) a (t a):=by ext1 i; by_cases h:i=a; subst i; simp[F]; simp[F,h]
          have hV: handle Z (Function.update (F s) a (t a)) x= handle Z (Function.update (F s) a (t' a)) x := congr_fun (congr_arg (fun v: foliage Z=> v.val) (h a)) ⟨n,x,F s,a,hx⟩
          rw [hu,hV,← show F s a=t' a from if_neg ha, Function.update_eq_self]; exact ih
    simpa only [show F Finset.univ=t from by ext1; simp [F]] using he Finset.univ
variable (Z)(h:Cresc Z)
noncomputable abbrev firstV(v: foliage Z):TagF:= (h.bell v).choose
lemma continued (t:Fin n→TagF):handle Z (firstV Z h ∘ signets Z ∘ t) x=handle Z t x:= stars hx _ _ (fun i=>(h.bell (signets ..)).choose_spec)
omit hx
noncomputable def sphere : (n:ℕ)→Points n→MultilinearMap ℂ (fun _ : Fin n=>foliage Z) ℂ:=fun n x=> if hx:x∈conf n then {
     toFun := fun u:Fin n→ foliage Z=> handle Z (firstV Z h ∘ u) x
     map_update_add' :=by
         intro dec u i b c -- decEq assumption.Local.
         obtain rfl : dec=instDecidableEqFin n:=Subsingleton.elim _ _; obtain ⟨d,p,q,rfl,rfl⟩:= h.allure b c; let f:=firstV Z h ∘ u
         have he(z:Label d): handle Z (firstV Z h ∘ Function.update u i (plume Z d z)) x= puts Z x f i d z:=by
             apply stars hx; intro j; by_cases hz:j=i; · subst j; rw [Function.comp_apply,update_self,update_self]; exact (h.bell ..).choose_spec
             rw [Function.comp_apply, Function.update_of_ne hz, Function.update_of_ne hz]; rfl
         rw[←map_add]; exact (he (p+q)).trans ((map_add ..).trans (congrArg₂ (·+·) (he _).symm (he _).symm))
     map_update_smul' :=by
         intro dec u i a b; obtain rfl : dec=instDecidableEqFin n:=Subsingleton.elim _ _; obtain ⟨d,p,hp⟩:= h.sealed b; rw[←hp,←map_smul]; let f:=firstV Z h ∘ u
         have he(z:Label d): handle Z (firstV Z h ∘ Function.update u i (plume Z d z)) x= puts Z x f i d z:=by
             apply stars hx; intro j; by_cases hz:j=i; · subst j; rw [Function.comp_apply,update_self,update_self]; exact (h.bell ..).choose_spec
             rw [Function.comp_apply, Function.update_of_ne hz, Function.update_of_ne hz]; rfl
         exact (he _).trans ((map_smul ..).trans (congr_arg (fun x:ℂ=> a • x) (he _).symm)) } else 0
include hx
lemma cosmos (t:Fin n→TagF)(w:Fin n→ foliage Z)(hw:∀ i,signets Z (t i)=w i): sphere Z h n x w=handle Z t x:=by
      unfold sphere; rw [dif_pos hx]; rw [show w=signets Z ∘ t from funext fun i=>(hw i).symm]; exact continued Z hx h t -- arg
omit hx
end Zodiac
end YM.Massive.Tarn
#print axioms YM.Massive.Tarn.Zodiac.cosmos
#check YM.Massive.Tarn.Zodiac.sphere
#check YM.Massive.Tarn.Zodiac.cosmos
#check YM.Massive.Tarn.Zodiac.firstV
