import YM.Pollen.Rill
import YM.Pollen.Bolt
set_option autoImplicit false
noncomputable section
namespace YM.Massive.PCAC
open QCD QCD.Lat Function Lattice Wilson Creek Grass Ledge Lat Finset NormedSpace RG Cove Cove.Send Filter Run
open MeasureTheory QCD.Grass.Ward
open scoped Topology BigOperators ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{k N:ℕ}{t a b:ℝ}{o: Site c} {P:BudgetPoint}
open Further.DenseMixedKernels
abbrev Stall (c:Side)(N:ℕ) := Grid c → Lat.Fields c N→L[ℂ]Lat.Fields c N
variable (x y:Stall c N)
variable (h: Suit o P a x) (hp: Suit o P b y)
include h
lemma Suit.beyond (he:a≤b): Suit o P b x:=by
    obtain ⟨A,hA,f,q,f',w,h1,h2,h3⟩:=h.lanes; exact {h with nng:=h.nng.trans he, lanes:=⟨A,hA,f,q,f',w,h1.trans he,h2,h3⟩}
lemma Suit.scaleF (s:ℂ) : Suit o P (‖s‖*a) (s • x):=by
    constructor
    · intro i; constructor; · intro a; change s • x i _= Grass.grade (s • x i _); rw[(h.bean i).grade,map_smul]
      intro v y; change s • x i _= (s • x i v)*y+v*(s • x i y); rw[(h.bean i).product,mul_smul_comm,smul_mul_assoc,smul_add]
    · exact fun U V hu=> congr_arg (s • ·) (h.haloS _ _ hu)
    · intro i g u; change s • x i _=slots N g (s • x _ _); rw[h.gauge,map_smul]
    · exact fun i A u hu=> (region _).smul_mem (h.bloc _ _ _ hu) s
    · intro i A he u hu; change s • x i u=0; rw [h.empty _ _ he _ hu, smul_zero]
    · intro i u; change ber _ (s • x i u)=0; rw[map_smul,h.law,smul_zero]
    · exact mul_nonneg (norm_nonneg _) h.nng
    obtain ⟨J,hJ,p,f,g,w,h1,h2,h3⟩:=h.lanes; refine ⟨J,hJ,p,s • f,fun i=> ‖s‖*g i,w,?_,fun i=> ?_,fun i=>?_⟩
    · simp_rw [mul_assoc]; rw [←mul_sum]; exact mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    · obtain ⟨hq,hF,hw,hp,hM,hQ⟩:= h2 i; exact ⟨hq,hF,mul_nonneg (norm_nonneg _) hw,hp.const_smul s,(fun U o=> (hM U o).linear (s • ContinuousLinearMap.id ℝ ℂ) (fun x=> (norm_smul s x).le) (norm_nonneg _)),hQ⟩
    rw [Pi.smul_apply,h3,smul_sum]; exact sum_congr rfl fun j _=> (smul_smul ..)
include hp
lemma Suit.plus : Suit o P (a+b) (x+y):=by
    constructor
    · intro i; constructor; · intro u; change x i _+y i _ =Grass.grade (x i u+y i u); rw [(h.bean i).grade,(hp.bean i).grade,map_add]
      intro u v; change x i _+ y i _=(x i u+y i u)*v+u*(x i v+y i v); rw[(h.bean i).product,(hp.bean i).product,add_mul,mul_add]; abel
    · exact fun U V hx=> congr_arg₂ (·+·) (h.haloS _ _ hx) (hp.haloS _ _ hx)
    · intro i g u; change x i _+ y i _=slots N g (x _ u+y _ u); rw[h.gauge,hp.gauge,map_add]
    · exact fun i A u hu=> (region _).add_mem (h.bloc _ _ _ hu) (hp.bloc _ _ _ hu)
    · intro i A he u hu; change x i _+ y i _=0; rw [h.empty _ _ he _ hu,hp.empty _ _ he _ hu,add_zero]
    · intro i u; change ber _ (x i _+ y i _)=0; rw[map_add,h.law,hp.law,add_zero]
    · exact add_nonneg h.nng hp.nng
    obtain ⟨I,hI,f,p',p,q,h1,h2,h3⟩:=h.lanes; obtain ⟨J,hJ,w,q',v,k,m1,m2,m3⟩:=hp.lanes; refine ⟨I⊕J,inferInstance,Sum.elim f w,Sum.elim p' q',Sum.elim p v,Sum.elim q k,?_,fun i=>?_,fun u=>?_⟩; · rw [Fintype.sum_sum_type]; exact add_le_add h1 m1
    · rcases i with i|i; exact h2 _; exact m2 _
    rw [Pi.add_apply,h3,m3, Fintype.sum_sum_type]; rfl
omit hp
end YM.Massive.PCAC
namespace YM.MassiveQCD.Sample.Basal
open QCD QCD.Lat Function Lattice Wilson Creek Grass Ledge Lat Finset NormedSpace RG Cove Cove.Send Filter Run
open MeasureTheory QCD.Grass.Ward Cupola Ribbon Plate Plate.Card Plate.Card.Iris Massive.PCAC
open scoped Topology BigOperators ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{k N:ℕ}{t a b v a1 a2 b1 b2:ℝ}{I:Type}[Fintype I](o:I→Site c){P:BudgetPoint}
variable (x y z:I→Stall c 6)(e f g:I→ℂ)(h:∀ i,Suit (o i) P a (x i))(hp:∀ i,Suit (o i) P b (y i))(hz:∀ i,Suit (o i) P (a+b) (z i))
local notation "K"=>Keys c 6
variable {D E V X:Type}(u:Grid c→ EvenA c 6)(Y1 Y2:Grid c→Patio (Keys c 6⊕Spine I))(Q:Set (Finset I))(he:∀ i∈ Q,i.card ≤1) (s:List I)(hS:s.Nodup)(hJ:∀ i,i∈s)
include h hp hz he hS hJ
local notation "R"=> rootR (Spine I) (Keys c 6) ∘ u
local notation "X'"=> deltaU o x h e s R
local notation "Y'"=> deltaU o y hp f s R
local notation "Z'"=> deltaU o z hz g s R
lemma CarryT.projection (X₁:Reel c 6 I D)(X₂:Reel c 6 I E)(V1:Cape.Lure c 6 I V)(V2:Cape.Lure c 6 I X)(hX:CarryT o X₁ V1 P t v a1 a2 Q ((X')+Y1))(hY: CarryT o X₂ V2 P t v b1 b2 Q ((Y')+Y2))(hv:0 ≤ v)(ht:1 ≤ t)(hw:∀ i U p, g i • z i U p=e i • x i U p+ f i • y i U p) : -- repl
     CarryT o (addReel 6 X₁ X₂) (plusLure V1 V2) P t v (a1+b1) (a2+b2) Q ((Z')+(Y1+Y2)):=by
    have hB:= plusE o X₁ X₂ V1 V2 hX hY hv ht
    refine {hB with take:= fun i hi V=>?_}; rw [← hB.take i hi V]; let A:= shutter K i; have hp' : A (Z' V)=A (X' V)+ A (Y' V):=by
             by_cases hx:i.Nonempty; swap; · unfold A; rw [not_nonempty_iff_eq_empty.mp hx,emptyM o z hz, emptyM o x h, emptyM o y hp, add_zero]
             obtain ⟨j,hj⟩:= Finset.card_eq_one.mp ((he i hi).antisymm (card_pos.mpr hx)); let s':=(R) V; let X1:EvenA c 6:= (vacR (Spine I) K) s';
             let MAT:= light _ X1; have hPl: pluck K ∅ s'= MAT :=(revive ..).symm
             let Ph:= (h j).bean V; let Pg:=(hp j).bean V; have hh (Y:Fields c 6→L[ℂ]Fields c 6) (p:Bean Y) : Plus (Y MAT):=Eq.trans (p.grade _).symm (congr_arg Y X1.property)
             let v':= (e j) • (⟨x j V MAT, hh _ Ph⟩: EvenA c 6); let w':= (f j) • (⟨y j V MAT, hh _ Pg⟩: EvenA c 6)
             have hξ:=rootPlus o x h (X:=u) V; unfold A; rw [hj]; have hk:shutter K {j} (Z' V)=slipU j (v'+w'):=partM o z hz g s s' j V _ hξ (hJ _) hS (by change e j • (x j V MAT)+f j • (y j V MAT)=_; rw [show pluck K ∅ s'=MAT from hPl]; exact (hw ..).symm ); rw [hk,map_add]; exact congr_arg₂ (·+·) (partM o x h e s s' j V v' hξ (hJ _) hS (by rw [hPl]; rfl)|>.symm) (partM o y hp f s s' j V w' hξ (hJ _) hS (by rw[hPl]; rfl)|>.symm)
    simp_rw [Pi.add_apply,map_add]; rw [hp']; abel
end YM.MassiveQCD.Sample.Basal
#print axioms YM.MassiveQCD.Sample.Basal.CarryT.projection
#print axioms YM.Massive.PCAC.Suit.plus
#print axioms YM.Massive.PCAC.Suit.scaleF
