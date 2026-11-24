import YM.Tinus.Cents
import YM.Profiles.ToneBank
/-! Sign charge. Exactly transferred: helps preserving lane comparison. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.PCAC
open Function Filter MeasureTheory Set QCD QCD.Lat QCD.Grass Lattice Wilson UV RG QCD.Grass.Ward
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator Classical TensorProduct Kronecker
variable {S:Scheme}{R c:Side}{d n i l j:ℕ}
open Poised Poised.Beacon Poised.Plans Finset Module Poised.Stative Massive.Patria Exposure
variable (x y a:Flavor 6) (p:Site c) (M:Spike) (h:x≠y)
local notation "T" =>localF p M x y
local notation "P"=>ribbonK a
noncomputable abbrev shaft (c:Side):= adapter (byFlavor (ribbonK a) (fun i:Modes c 6=>i.2)) (byFlavor (ribbonK a) (fun i:Modes c 6=>i.2))
lemma dusk (a:Flavor 6)(y:Density c 6) : Cylinder.Action.flavor (ribbonK a) y = shaft a c∘ y:=by
    unfold Cylinder.Action.flavor Cylinder.Action.flavorF shaft byFlavor ribbonK; simp; rfl
lemma c_spark {A:Type*} [Fintype A](D:Sour A)(g:Bool)(i:Dirac A): applyMark g (-D) i= - applyMark g D i:=by cases g<;> simp only [column,row,Matrix.neg_apply,neg_smul,sum_neg_distrib]
include h
lemma L_odd (g:Bool)(hd:a=x∨a=y)(i:Lat.Fields c 6): shaft a c (ore p g x y M i)= -(ore p g x y M (shaft a c i)):=by
     let A:=byFlavor (ribbonK a) (fun i:Modes c 6=>i.2); let V:=localF p M x y; let k:= shaft a c; have hx:A*V= -(V*A):=by
          unfold A byFlavor; ext i j; rw [Matrix.diagonal_mul,Matrix.neg_apply,Matrix.mul_diagonal]; by_cases hv:i.2=x ∧ j.2=y
          · obtain hx|hx:=hd; all_goals simp only [ribbonK,bandK,hv.1,hv.2,hx]; first|simp [h,h.symm] -- both
          have hp : V i j=0:=by unfold V localF; rw[zleft]; unfold flavorW; simp [spot,hv]
          rw [hp, mul_zero,zero_mul, neg_zero]
     change k (applyMark _ _ i) = - applyMark _ _ _; have hv := L_slope g A A (-V) V (by rw [mul_neg,hx,neg_neg]) (by unfold A byFlavor; rw [Matrix.diagonal_transpose,neg_mul]; exact hx.symm) i; exact hv.symm.trans (c_spark V g _)
variable (A:Massive.Run S n R 6) (hA:A.Actual)
variable (u:Averaging)(g:Bool)
-- local notation "Xt"=> report A (stalk M A x y g l) u
open Massive.Patria.Depth
include hA
lemma mindful (ht:i≤ l)(hl:l≤ n)(hx:a=x∨a=y)(b:Cover): Cylinder.Action.flavor (ribbonK a) (Depth.report A (stalk M A x y g l) u i b)= -⇑(Depth.report A (stalk M A x y g l) u i b):=by
     let Pz:=actor A l; let Y:= stalk M A x y g l; let Z(k:ℕ)(b:Cover):= Depth.report A Y u k b
     have hT: TideT A u l Z:= stagger M A u hA x y g hl
     induction ht using Nat.decreasingInduction generalizing b with
     | self =>
        rw [Depth.arrivesHere]; have heP:Cylinder.Action.flavor (ribbonK a) (⇑Pz)=⇑Pz:=by unfold Pz; rw[act A hA hl,pier A hA hl]; exact (arrives A l hl).2.2.1 _
        rw [dusk]; funext U; change shaft a _ (ore (wrap _ b) _ _ _ _ _) = -(ore _ _ _ _ _ (Pz U)); nth_rw 2 [←show Cylinder.Action.flavor (ribbonK a) _ U =Pz U from congr_fun heP U]; rw [dusk]; exact L_odd x y a _ M h g hx _
     | of_succ i ht ih=>
        obtain ⟨Q,hQ,hE,f,t,h1,h2,h3,h4⟩:= Massive.Patria.Rolls.constitution (X:=Cover→₀ℝ) u (stitch S R i|>.ratio); let c:= S.side R i; let v(σ:Q):= Z (i+1) ((S.step i).L.val • b+t σ); have he:⇑(Z i b)=∑ j,(f j:ℂ) • A.block i (v j):= hT.steps i ht Q f t h4 b
        have hh(j:Q):Cylinder.Action.flavor (ribbonK a) (A.block i (v j))= -A.block i (v j):=by
             unfold Run.block; rw [Patria.step_brute]; rw [Patria.Exposure.flavor_shift _ _ (S.admissible _) _ _ (ContinuousMap.continuous _), show Cylinder.Action.flavor _ (v j)= _ from ih _]
             rw [← step_brute, ← step_brute]; exact congr_arg DFunLike.coe (map_neg (S.send R A.β A.w i) (v j)) -- scope
        change Cylinder.Action.flavor _ (⇑(Z i b))=-⇑(Z i b); rw[dusk, he]; funext V; simp only [Function.comp_apply, Pi.neg_apply,Finset.sum_apply,Pi.smul_apply,map_sum,map_smul, ←sum_neg_distrib]; apply sum_congr rfl; intro j _; rw [show shaft a _ (A.block i (v j) V)= _ from congr_fun ((dusk a _).symm.trans (hh j)) V]; exact smul_neg ..
variable (X:Label 8)(W:SourceRead.TaperHol)(B:Bore 8)(q:Market S R 8)(hW:Wager A W B q i)(s:RawSym)(hp: Rubric s B)
include hW hp
lemma ignite (ht:i≤l)(hl:l≤ n)(hz:Tally W 0 X (A.density i) (Depth.report A (stalk M A x y g l) u i 0)) : Poised.Plans.Stamp.Stair.OffS X:=by
     have hd(a:Flavor 6)(hv:a=x∨a=y): flavorAct (ribbonK a) X.val= - X.val:=by
         let G:=Depth.report A (stalk M A x y g l) u i 0; let r:= ribbonK a; have hP:Cylinder.Action.flavor r (A.density i)=A.density i:=by rw [pier A hA (ht.trans hl)]; exact (Depth.arrives A i (ht.trans hl)).2.2.1 r
         have he:=Canvas.arrows W r (G) (s.flavor 8 r X) (fun x:UV.Label 8=>⇑(B (S.side R i) 0 x)) hz hW.reading hP (hp.flavor (S.side R i) X 0 r); change Tally _ _ _ _ (Cylinder.Action.flavor _ G) at he -- order
         rw [show Cylinder.Action.flavor r G= -⇑G from mindful x y a M h A hA u g ht hl hv _] at he; have hx:= QCD.Acre.Stratum.MarchQ.Suburb.Melt.Lobby.Talent.shines W 8 0 X (-1) _ _ hz; simp only [neg_one_smul] at hx; rw [←s.flavorActs, Canvas.consensus _ _ _ he _ hx]; change (- (1:ℂ)) • X.val=-X.val; exact neg_one_smul ℂ X.val
     exact thickness x y X h (hd x (.inl rfl)) (hd y (.inr rfl))
end YM.Massive.PCAC
#print axioms YM.Massive.PCAC.ignite
