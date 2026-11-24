import YM.QCD.Globe.Folly
import YM.QCD.Nola.Wheat
import YM.QCD.Nola.Arch
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Globe
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Pine YM.Next.Free Leaf LeafM Tee Garden Entr Kites
variable {f c:Side}{j k m N:ℕ}{S:Flight j k} {h:f.val=c.val*S.L.val}{p:BudgetPoint}
section
variable {A: Type*}[Fintype A][DecidableEq A](f:Alg A →ₐ[ℂ] Alg A)(p:Equiv.Perm A)(g:A→ℂ)
lemma pens (i:Finset A)(he:∀ i,f (atom i)=g i • Grass.atom (p i))(ht:∀ i,‖g i‖=1) :∃ c:ℂ, ‖c‖=1 ∧ f (mono i)=c • mono (i.image p):=by
    induction i using Finset.induction_on with
    | empty=> exact ⟨1,norm_one,by simp⟩
    | insert a i ha ih=>
        have hp:Disjoint {a} i:=by simp [ha]
        have hz:Disjoint {p a} (i.image p):=by simp [ha]
        obtain ⟨c,hc,hu⟩:=ih
        have hF :f (mono {a}*mono i)=(g a*c) • (mono {p a}*mono (i.image p)):=by rw [map_mul,hu, mono_single,he,mono_single, smul_mul_smul_comm]
        have hh :‖g a*c‖=1:=by rw [norm_mul, ht,hc,mul_one]
        rw [image_insert]; obtain hv|hv:=mono_mul_sign _ _ hp <;> rw [hv,disjUnion_eq_union,singleton_union] at hF <;> obtain h|h:=mono_mul_sign _ _ hz <;> rw [h,disjUnion_eq_union,singleton_union] at hF
        · exact ⟨_,hh,hF⟩
        · exact ⟨-(g a*c),by rw [norm_neg,hh],by rw [hF]; simp⟩
        · exact ⟨-(g a*c),by rw [norm_neg,hh],by rw [neg_smul,← hF,map_neg]; simp⟩
        simp only [smul_neg,map_neg,neg_inj] at hF; exact ⟨_,hh,hF⟩
lemma directS (hp:∀ i,f (Grass.atom i)=g i • Grass.atom (p i))(ht:∀ i,‖g i‖=1)(X: Alg A)(h:f X=X)(S:Finset A): ‖coef (S.image p) X‖ =‖coef S X‖:=by
     obtain ⟨d,hd,hD⟩:=pens f p g S hp ht
     have he: coef (S.image p) (f X) = d*(coef S X):=by
          conv_lhs=> rw [← write X,map_sum,map_sum]
          rw [sum_eq_single S]
          · rw [map_smul,hD,map_smul,map_smul,Grass.read]; ring
          · intro i _ hh; obtain ⟨t,_,hv⟩:=pens f p g i hp ht; rw [map_smul,hv,map_smul,map_smul,Grass.read_other _ _ _,smul_zero,smul_zero]; exact fun h=> hh ((Finset.image_injective p.injective) h.symm)
          simp
     rw [h] at he; rw [he,norm_mul,hd,one_mul]
end
open Nola
variable (o: Site c)(F:EvenA c N)
noncomputable def ports (N:ℕ)(o:Site c) : Equiv.Perm (Modes c N):= Equiv.prodCongr (Equiv.prodCongr (Equiv.addRight o) (Equiv.refl (Lat.Fiber))) (Equiv.refl _)
noncomputable def portS (N:ℕ)(o:Site c) : Equiv.Perm (Keys c N):= Equiv.sumCongr (ports N o) (ports N o)
lemma portAt (N:ℕ)(i:Keys c N):locationP (portS N o i) = locationP i+o:=by cases i <;> rfl
set_option quotPrecheck false
local notation "R" => Strut.haze (1,o)
lemma visitH (N:ℕ)(g:Site c→ℂ)(h:Warrant (1,o) g 1)(i:Keys c N): disguise (copies N (R 1 g)) (atom i)= g (locationP i) • atom (portS N o i):=by
    let M:=copies N (R 1 g)
    have he(j k: Modes c N):M j k= if ports N o j=k then g j.1.1 else 0:=by
         unfold M copies Strut.haze Revolve.hues; rw [Matrix.blockDiagonal_apply]; split
         next hu=>
             rw [rr,star_one,wave_one]; change (if j.1.1+o=k.1.1 then _ else _)= if (((j.1.1+o,j.1.2),j.2) : Modes c N)=k then _ else _; have he:(((j.1.1+o,j.1.2),j.2) : Modes c N)=k↔ j.1.1+o=k.1.1∧ j.1.2=k.1.2:= by rw [Prod.ext_iff, Prod.ext_iff (x:= _)]; simp [hu]
             simp only [he]; by_cases hx:j.1.1+o=k.1.1 <;> by_cases hv:j.1.2=k.1.2 <;> simp [hx,hv,Matrix.one_apply]
         next hu=> rw [if_neg]; exact fun hv=> hu (show (ports N o j).2=k.2 from congr_arg Prod.snd hv)
    cases i
    next i=> change adapter M _ (psi i)=g _ • psi (ports N o i); rw [adapt_psi]; simp_rw [he,ite_smul,zero_smul]; rw [sum_ite_eq,if_pos (mem_univ _)]; rfl
    next i=> change adapter M (star M)ᵀ (bar i)= g _ • bar _; rw [adapt_bar]; simp only [Matrix.transpose_apply,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply, he]; simp_rw [apply_ite star,star_zero,ite_smul,zero_smul]; rw [sum_ite_eq,if_pos (mem_univ _)]; change star (g i.1.1) • bar _=g i.1.1 • bar _; rcases h.1.sign i.1.1 with h|h<;>simp[h] -- adjust
lemma Cocoa.away (h: Cocoa F)(i:Finset (Keys c N)):‖coef (i.image (portS N o)) F.val‖=‖coef i F.val‖:=by
    obtain ⟨g,hg⟩:= shades 1 (0:Site c) 0 o; have hp: Warrant (1,o) g 1:= ⟨hg,Swing.none⟩; refine directS (disguise (Lat.copies N (R 1 g))) _ (fun i=>g (locationP i)) (visitH o N g hp) (fun i=>?_) F.val (congr_arg Subtype.val (h.cream _ _ _ hp)) i
    rcases hg.sign (locationP i) with hi|hi<;> simp [hi]
end YM.QCD.Globe
