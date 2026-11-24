import YM.Tawny.Cush
import YM.Oriole.Finical
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tawny
open QCD QCD.Lat QCD.Grass Lattice TensorProduct Function UV PCAC
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator ContDiff Classical TensorProduct
variable {d:ℕ}(a b:Flavor 6)
open Poised.Display Poised.Stative Module Finset Oriole
local notation "T" => SpinMode d
local notation "Ae" => Pairs T
local notation "W"=>CensusA d
noncomputable def ray (J:Labels.Taylor su 0) : Pol d→ₗ[ℂ] W:= skin (Pi.single 0 J)-skin 0
variable (J:Labels.Jet su) (X:GPol)
local notation "T₀"=>SpinPol d
local notation "Y"=> ready d J
local notation "Δ"=> skin (d:=d) J
local notation "Δ₀"=> skin (d:=d) (0:Labels.Jet su)
namespace Pane
abbrev SubS (S:W)(n:ℕ):Prop:=∀ i j:T,S i j≠ 0→i.2=j.2 ∧ spinWeight i.1.1+spinWeight j.1.1+n≤d
noncomputable def ShellG(n:ℕ):Submodule ℂ W where
  carrier:={x| SubS x n}
  add_mem':=by
       intro x y h k i j hz; by_contra hv; have he : x i j= 0:= Classical.byContradiction fun w=>hv (h i j w); have hu : y i j=0:= Classical.byContradiction fun w=>hv (k i j w); simp[he,hu] at hz
  zero_mem':= fun _ _ hu=> False.elim (hu rfl)
  smul_mem':=by intro z x h i j hz; exact h i j (fun he=>hz (by rw [Matrix.smul_apply,he,smul_zero]))
structure KitP (x:Pol d) : Prop where
  lean : Δ₀ x ∈ ShellG 0
  loop : ∃ P:Labels.Taylor su 0→ₗ[ℝ] W,(∀ J:Labels.Jet su,skin J x=Δ₀ x+ P (J 0))∧∀ J:Labels.Taylor su 0,P J∈ ShellG 4
noncomputable def shelf : Submodule ℂ (Pol d) where
 carrier:={x|KitP x}
 add_mem':=by
     intro x y ⟨hl,K,hK,k⟩ ⟨hm,T',hT,t⟩; refine ⟨map_add Δ₀ x y ▸ ?_,K+T',fun J=>?_,fun J=>?_⟩ -- equality rewrit wrong direction
     · exact Submodule.add_mem _ hl hm
     · rw [map_add,map_add,hK,hT]; change _=_+(K _ + T' _); abel
     exact Submodule.add_mem _ (k J) (t J)
 zero_mem':=⟨by rw [map_zero]; exact Submodule.zero_mem _,0,by simp,fun _=>Submodule.zero_mem _⟩
 smul_mem':=by
      intro z x ⟨he,K,h,k⟩; refine ⟨?_,(z • K),fun J=>?_,fun J=>?_⟩; rw [map_smul]; exact Submodule.smul_mem _ _ he
      rw [map_smul,map_smul,h,smul_add]; rfl
      exact Submodule.smul_mem _ _ (k J)
private lemma splits_one (p : Powers) (hp : p≠0) : ∃ i : Labels.Key su,∃ q:Powers,p=q+Finsupp.single i 1 := by
  obtain ⟨i,h⟩ : p.support.Nonempty := by simpa using hp
  have ht : Finsupp.single i 1 ≤ p := by
    intro x; by_cases he : x=i
    · subst x; rw [Finsupp.single_eq_same]; exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp h)
    simp [Ne.symm he]
  exact ⟨i,p-Finsupp.single i 1,(tsub_add_cancel_of_le ht).symm⟩
variable (i k:SpinMode d)
private lemma enough (m:Powers)(p q:T): let P:PowerPair d:=(m,{Sum.inr p,Sum.inl q}); weight P=2*Labels.height m + (spinWeight p.1.1+spinWeight q.1.1):=by intro Q; unfold UV.weight; rw [show Q.2={Sum.inr p,Sum.inl q} from rfl, sum_pair (by intro h; cases h)]; rfl
private lemma book {m:Powers}(he:i.2=k.2)(hd:d≤10)(hk: weight (d:=d) (m,{Sum.inr i,Sum.inl k})≤d) : MvPolynomial.monomial (σ:=Labels.Key su) m 1 ⊗ₜ[ℂ] (bar i *psi k) ∈ shelf:=by
   let B : W:= Matrix.single i k 1
   have ht:=enough m i k; change _ = _ at ht; rw [show weight (m,{Sum.inr i,Sum.inl k})=_ from ht] at hk
   let r:=2*Labels.height m; have hb : B∈ ShellG r:=by
       intro a b H₀; unfold B at H₀; rw [Matrix.single_apply] at H₀; split at H₀; next h=> obtain ⟨rfl,rfl⟩:=h; exact ⟨he,(add_comm _ r) ▸ hk⟩
       next _=> exact False.elim (H₀ rfl)
   have hs:= Oriole.low i.1.1; have hz:= Oriole.low k.1.1; refine ⟨?_,?_⟩
   · rw [bought_skin]; change _ • B∈_; have hB: B ∈ ShellG 0:=fun p q h=> ⟨(hb p q h).1, add_le_add (le_refl _) (Nat.zero_le r) |>.trans (hb p q h).2⟩; exact Submodule.smul_mem _ _ hB
   by_cases h0:m=0
   · subst m; refine ⟨0,fun J=>?_,fun J=>Submodule.zero_mem _⟩; change skin J ((1:GPol)⊗ₜ[ℂ]_) = Δ₀ ((1:GPol)⊗ₜ[ℂ]_) +0; rw [bought_skin,bought_skin,map_one,map_one, add_zero]
   obtain ⟨⟨j,l⟩,p,hp⟩:= splits_one m h0; have hm : j=0∧p=0:=by
      have ht : Labels.height m = Labels.height p + (j+2):=by rw[hp,Labels.height,map_add,Finsupp.weight_single,one_smul]; rfl
      constructor
      · rw [ht] at hk; omega
      by_contra hh; obtain ⟨y,u,H⟩:=splits_one p hh; have he:Labels.height p=Labels.height u+ (y.1+2):=by rw [H, Labels.height,map_add,Finsupp.weight_single,one_smul]; rfl
      rw [ht,he] at hk; omega
   obtain ⟨hj,hp'⟩:=hm; subst j p; rw [zero_add] at hp; have he:r=4:=by unfold r; rw [hp,Labels.height,Finsupp.weight_single,one_smul]; rfl
   let L:Labels.Taylor su 0→ₗ[ℝ]ℝ:= (Labels.axes su 0).coord l; refine ⟨L.smulRight B,fun J=>?_,fun J=> ?_⟩
   · rw[bought_skin,bought_skin,hp]; change Labels.read J (MvPolynomial.X _) • B=Labels.read (0:Labels.Jet su) (MvPolynomial.X _) • B+_; rw [Labels.read,Labels.read,MvPolynomial.aeval_X, MvPolynomial.aeval_X,show Labels.coord (0:Labels.Jet su) ⟨0,l⟩=0 from ?_,zero_smul,zero_add]; · rw [LinearMap.smulRight_apply,← Complex.coe_smul]; rfl -- inspect
     simp [Labels.coord]
   rw [he] at hb; rw[LinearMap.smulRight_apply,← Complex.coe_smul]; exact Submodule.smul_mem _ _ hb
variable (j:Rings d)(x:Label d)(h:Quiet x.val)(hd:d≤10)
include h hd
lemma garner(hp:coord j.val x.val≠0): gen j.val∈shelf:=by
    let G:GPol:= MvPolynomial.monomial j.val.1 1; rcases orderR x j h hd hp with hT|⟨i,k,h',hz⟩
    · rw [show gen j.val= G⊗ₜ[ℂ](1:T₀) from by unfold UV.gen; rw [hT,mono_empty]]; refine ⟨by rw[unit_skin]; exact Submodule.zero_mem _,0,fun J=>?_,fun J=>Submodule.zero_mem _⟩; rw [unit_skin,unit_skin]; simp
    have he := book (m:=j.val.1) i k h' hd (Eq.subst (motive:=fun P:PowerPair d=>weight P ≤ d) (show j.val=(j.val.1,{Sum.inr i,Sum.inl k}) from Prod.ext rfl hz) (upper j))
    change G⊗ₜ[ℂ] mono j.val.2 ∈ _; rw [hz]; rcases bladeX (Sum.inr i) (Sum.inl k) (by intro h; cases h) with hx|hx; · rw [← hx]; exact he
    rw [show mono {Sum.inr i,Sum.inl k}= -(atom (Sum.inr i)*atom (Sum.inl k)) from by rw [hx,neg_neg], tmul_neg]; exact Submodule.neg_mem _ he
lemma stocks : KitP x.val:=by
    change x.val∈ shelf; rw [← quiet x.val ((label_law _).mp x.property).1]; change ∑ i:Rings d,_∈shelf; refine Submodule.sum_mem _ fun j _=>?_ ; by_cases ht:coord j.val x.val=0; rw [guide,ht,zero_smul]; exact Submodule.zero_mem _
    exact Submodule.smul_mem _ _ (garner j x h hd ht)
noncomputable def glow : Labels.Taylor su 0→ₗ[ℝ] W:= (stocks x h hd).loop.choose
local notation "Ψ"=> glow x h hd
lemma shiny : Δ x.val= Δ₀ x.val+ Ψ (J 0):= (stocks x h hd).loop.choose_spec.1 J
lemma glean (J:Labels.Taylor su 0): ray J x.val= Ψ J:=by unfold ray; rw [LinearMap.sub_apply,shiny _ x h hd]; simp
lemma outer (A:Labels.Taylor su 0)(hu:d<10) : Ψ A=0:=by
    let Q:= Ψ A; have hP : Q ∈ ShellG 4:= (stocks x h hd).loop.choose_spec.2 _
    ext i j; change Q i j=0; by_contra ht; have hz:spinWeight i.1.1+spinWeight j.1.1+4 ≤ d:= (hP i j ht).2; have he:=Oriole.low i.1.1; have hm:=Oriole.low j.1.1; omega
end Pane
end YM.Massive.Tawny
#print axioms YM.Massive.Tawny.Pane.glean
