import YM.Tawny.Viola
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
local notation "U"=> (0:Multi 10)
local notation "Z"=> RawVec 10
variable (x:RawVec 10)
set_option quotPrecheck false
local notation "X" i:arg=> (x.val i).val
local notation "g" p:arg q:arg i:arg=>prism0 a p q (x.val i).val
local notation "L" i:arg=> leadR i
local notation "H" i:arg j:arg=> ηR i j
variable (p q:Multi 10)(i j k l:Axis)
open StressFlux.Offer
local notation "hR" i:arg j:arg k:arg=> prism1 a U U j k (X i)
noncomputable def read0 : Z→ₗ[ℂ]Spike:= prism0 a p q ∘ₗ (labels _).subtype ∘ₗ LinearMap.proj i ∘ₗ (Z).subtype
noncomputable def readX : Z→ₗ[ℂ]Spike:=prism1 a U U j k ∘ₗ (labels _).subtype ∘ₗ LinearMap.proj i ∘ₗ (Z).subtype
noncomputable def core0 : Z→ₗ[ℂ](Fin 7 →ℂ):= LinearMap.pi (![
    feeP [0,0] ∘ₗ read0 a U (L 0) 0,
    feeP [0,1] ∘ₗ read0 a U (L 1) 0,
    feeP [0,0,0] ∘ₗ read0 a U (H 0 0) 0,
    feeP [0,1,1] ∘ₗ read0 a U (H 1 1) 0,
    feeP [0,0,1] ∘ₗ read0 a U (H 0 1) 0,
    feeP [0,0,1] ∘ₗ read0 a (L 0) (L 1) 0,
    feeP [0,0,1] ∘ₗ readX a 0 0 1
    ])
variable (ht:core0 a x=0)
private lemma par (Xv:Spike)(p:EuPin)(h:Xv=0): conjug p Xv=0:=by rw[h,conjug,mul_zero,zero_mul]
include ht
lemma rootL : g U (L k) i=0:=by
     by_cases h:k=i
     · let P:=Equiv.swap 0 i; obtain ⟨w,hw⟩:= EuPin.choice (flag P); have hP:= passP a x U (L 0) 0 P w hw; rw[hem_ground, hem_lead, show (flag P).perm 0=i from Equiv.swap_apply_left ..,show P 0=i from Equiv.swap_apply_left ..] at hP; subst k; rw[hP]; exact par _ _ (germ _ _ (congr_fun ht 0) (grL a x 0 0))
     obtain ⟨P,hP,hV⟩:= StressFlux.extend_two i k (Ne.symm h); obtain ⟨w,h⟩:=EuPin.choice (flag P); have he:=passP a x U (L 1) 0 P w h; rw [hem_ground,hem_lead,hP,show (flag P).perm 1=k from hV] at he; rw[he]; exact par _ _ (germ _ _ (congr_fun ht 1) (grL a x 0 1))
lemma rootP (i k:Axis)(h:i≠k): g (L i) (L k) i=0∧g U (H i k) i=0 ∧hR i i k=0:=by
     obtain ⟨P,hP,hV⟩:=StressFlux.extend_two i k h; obtain ⟨w,hw⟩:=EuPin.choice (flag P); have h1:(flag P).perm 1=k:=hV; have h0:(flag P).perm 0=i:=hP
     constructor
     · have he:= passP a x (L 0) (L 1) 0 P w hw; rw [hem_lead,hem_lead,hP,h1,h0] at he; rw[he]; exact par _ _ (germ _ _ (congr_fun ht 5) (grP a x 0 0 1))
     constructor
     · have he:= passP a x U (H 0 1) 0 P w hw; rw [hem_ground,hem_η,hP,h1,h0] at he; rw [he]; exact par _ _ (germ _ _ (congr_fun ht 4) (grS a x 0 0 1))
     have he:= passX a x 0 0 1 P w hw; rw [hP,hV] at he; rw[he]; exact par _ _ (germ _ _ (congr_fun ht 6) (grX a x 0 0 1))
lemma rootHi (k:Axis): g U (H k k) i=0:=by
    by_cases h:i=k
    · subst k; let P:=Equiv.swap 0 i; obtain ⟨w,hw⟩:=EuPin.choice (flag P); have ht':=passP a x U (H 0 0) 0 P w hw; rw [hem_ground,hem_η,show P 0=i from Equiv.swap_apply_left .., show (flag P).perm 0=i from Equiv.swap_apply_left ..] at ht'; exact ht'.trans (par _ _ (germ _ _ (congr_fun ht 2) (grS a x 0 0 0)))
    obtain ⟨P,hP,hV⟩:=StressFlux.extend_two i k h; obtain ⟨w,h⟩:=EuPin.choice (flag P); have he:=passP a x U (H 1 1) 0 P w h; rw [hem_ground,hem_η,hP,show (flag P).perm 1=k from hV] at he; exact he.trans (par _ _ (germ _ _ (congr_fun ht 3) (grS a x 0 1 1)))
lemma rootS : g U (H j k) i=0∧g (L j) (L k) i=0∧hR i j k=0:=by
    rcases eq_or_ne j k with hz|hz; · subst k; exact ⟨rootHi a x i ht j, diag_kill a x i j, twin0 a x i j⟩
    rcases eq_or_ne i j with hu|hu; · subst j; have hp:= rootP a x ht i k hz; exact ⟨hp.2.1,hp.1,hp.2.2⟩
    rcases eq_or_ne i k with hv|hv
    · subst k; obtain ⟨h1,h2,h3⟩:= rootP a x ht i j hu; rw[H_swap j i,tollP a x (L i) (L j),swapX a x i j i,h2,h1,h3,neg_zero,truck_blank]; exact ⟨rfl,rfl,rfl⟩
    obtain ⟨h,h'⟩:=combo a x i j k hu hv hz; exact ⟨h,h',vanishX a x i j k hu hv hz⟩
lemma pixel (hp:spinWeight p+spinWeight q≤10) : g p q i=0:=by
    have hL:= fun j=>rootL a x i j ht; have hQ:= fun j k=>rootS a x i j k ht; rcases sky p q hp with ⟨h,v|⟨j,v⟩|⟨j,k,v⟩⟩ | ⟨v,⟨j,h⟩|⟨j,k,h⟩⟩| ⟨j,k,h,v⟩ <;> subst p q
    · exact gr0 a x i
    · exact hL j
    · exact (hQ j k).1
    · rw [tollP a x U,hL,truck_blank]
    · rw [tollP a x U,(hQ _ _).1,truck_blank]
    exact (hQ j k).2.1
omit ht
instance: AddCommGroup Z:= Submodule.addCommGroup (R:=ℂ) (M:=Axis →Label 10) (p:=Z)
noncomputable def detector : Z→ₗ[ℂ](OneG su × (Flavor 6→Fin 7→ℂ)):=
    (show Z→ₗ[ℂ] OneG su from valet Vc signT id 1 (d:=10) (by decide)).prod (LinearMap.pi fun a=>core0 a)
open LinearMap
local instance : AddCommGroup (OneG su):= Submodule.addCommGroup _
lemma rankV : Injective detector:=by
    refine (LinearMap.ker_eq_bot (R:=ℂ) (R₂:=ℂ) (M:=Z) (M₂:=OneG su × (Flavor 6→ Fin 7→ℂ)) (f:=detector)).mp (ker_eq_bot'.mpr ?_); intro x h; apply Subtype.ext; funext i; have hv:=show Meaning _ _ _ _ 10 _ from x.property; have hT(a):core0 a x=0:= congr_fun (congr_arg Prod.snd h) a
    apply denovo _ (hv.light i) (by decide) (congr_arg Subtype.val (congr_fun (congr_arg Subtype.val (congr_arg Prod.fst h)) i)) (fun a p q=> pixel a x p q i (hT a)); intro a p q h k l; have hp:= Oriole.low p; have hq:= Oriole.low q; rw [ground p (by omega),ground q (by omega)]; exact (rootS a x i k l (hT a)).2.2
lemma highR : Module.finrank ℂ (RawVec 10) ≤ 45:=by
    have he:= LinearMap.finrank_le_finrank_of_injective rankV; haveI:Module.Free ℂ ↥(OneG su):=Module.Free.of_divisionRing ℂ (OneG su); rw [Module.finrank_prod,Module.finrank_pi_fintype] at he; have ht:= (rankRG QCD.simple).2; simp only [Module.finrank_fin_fun,Flavor,sum_const,card_univ, Fintype.card_fin,nsmul_eq_mul] at he; omega
end Cast
end YM.Massive.Tawny
#print axioms YM.Massive.Tawny.Cast.highR
