import YM.Tinus.Wreath
import YM.Lyre.Range
import YM.HONE.Eyes
import YM.HONE.Hearth
import YM.TIPS.Fall
import YM.Patria.Canons
import YM.Patria.Calm
/-! # Orion MR masks authenticated matched sensor. -/
set_option autoImplicit false
noncomputable section
namespace YM.Intag
open Function Filter MeasureTheory RG
open Lattice Wilson Cells YM.Next.Rank.Station
open Massive Massive.Lyre Massive.Patria.Hub Massive.Patria.Depth Massive.Romance QCD QCD.Tide Push.GridApprox QCD.Lat QCD.Grass MassiveQCD MassiveQCD.Cupola
open scoped BigOperators Classical
namespace CardsT
open Pilgrim Tess Column Finset Plum UV
variable {S:Scheme}{R:Side}{k i ℓ p n:ℕ}(A:Massive.Run S n R 6)
local notation "Pr"=> Site (S.side R p)
variable (z:Site (S.side R ℓ))(hj:p ≤ ℓ)(hp:Even R.val)(P:Site (S.side R p))(x:Cover)
set_option quotPrecheck false
local notation "T"=> mural (viewW S R hj) (evenW S R hp p) z
local notation "X" => Pilgrim.bout T P rfl x
local notation "uP" j:arg=> μ T P j
local notation "κ" t:arg=> (mural (viewW S R hj) (evenW S R hp p) z).bandCut (post (mural (viewW S R hj) (evenW S R hp p) z) P t).1 (post (mural (viewW S R hj) (evenW S R hp p) z) P t).2
variable (U:Averaging)(Wq:Site (S.side R p) → Cover → Insertion (S.side R i) 6)
open Massive.Patria
local notation "Δq" u:arg=> tentT A U (Wq u)
open Poised Poised.Plans Poised.Display
variable {V0: YM.Source.Hol su}(A0: Lining.Temper.Collage.Exhibit V0)(η₀:SourceRead.TaperHol)(sy:RawSym) (d:ℕ)(pB: Site (S.side R p) → UV.Label d)(t:ℕ) (Q:PatchMix d) (hO: OrderMix A η₀ sy (Massive.Patria.Depth.Bloom A0 d) (i:=t) Q)
local notation "Qb"=>Massive.Patria.Depth.Bloom A0 d
local notation "Yq"=> fun (j:Pr)(b:Cover)=> Massive.Patria.Depth.Bloom A0 d (S.side R n) b (Q U (pB j))
variable (hR:Rubric sy (Massive.Patria.Depth.Bloom A0 d))(hA:A.Actual) (σ:Site (S.side R p)→Bool)(hi:ℓ≤ i)(ht:t≤ ℓ)(hv:i≤ n)
-- y normalized *before conversion to engineering real factors*. can scale norm power later.Mon.Transmission.M.
local notation "T★"=> Column.sky S R p n (hj.trans (hi.trans hv)) (evenW S R hp p) z
include hR hO hi ht hv hA
open MassiveQCD.Sample
local notation "Dk"=> Hole (Site (S.side R p)) S ℓ ℓ
set_option maxHeartbeats 580000 in
lemma chamberQ (hM:∃ w:Market S R d,Wager A η₀ (Massive.Patria.Depth.Bloom A0 d) w t)(hFt:∀ j,moored (Q U (pB j)).val (σ j))
   (hT:∀ j,Tally η₀ 0 (pB j) (A.density t) (Massive.Patria.Depth.report A (Wq j) U t 0))(hτ:∀ v:Pr,v≠P→∀ b:Cover, Cylinder.Action.adj (κ v).pos (Wq (uP v) b)= Wq v ((κ v).flip.act b)): ∃ (m:ℕ)(f:Fin m→Hole (Site (S.side R p)) S ℓ ℓ),Quills.crest f= Finset.univ ∧ Injective f ∧ ‖valueH A.regulator (CardsT.rolledT X (fun _=>U) Yq m f)‖=topH (sky S R p n (hj.trans (hi.trans hv)) (evenW S R hp p) z) A.regulator ⇑(checkedT U (ratioTo S n ℓ) (Yq P) x) P ^ Fintype.card (Site (S.side R p)):=by
    obtain ⟨w,hW⟩:= hM; let V:Pr→ Cover→ Insertion (S.side R ℓ) 6:=0; let g:= Yq; let Z:= (X:Pr→ Cover); let d':= V
    have hx:∀ t:Pr,t≠P→∀ b:Cover, Cylinder.Action.adj (κ t).pos (g (uP t) b)= g t ((κ t).flip.act b):=by
         intro j h b; let i:= uP j; let a:= (κ j).pos; have hp:= resolveR A hA hv (ht.trans hi) a U (Wq i) (Wq j) (hτ j h) (pB i) η₀ (Qb) sy hR w hW (hT i)
         let W:= Q U (pB i); have hx := Massive.Patria.Canvas.consensus η₀ 0 _ (hT j) _ hp; change Cylinder.Action.adj a (Qb (S.side R n) b W) = (Qb (S.side R n) _ (Q U (pB j))); rw[hx,←hO.eyeO U (pB i) a]; exact hR.eye (S.side R n) W b a
    obtain ⟨m,f,hp',hf,hV⟩:= stellar A z hj hp P x σ U g d' le_rfl (hi.trans hv) (fun j a b=>funext fun U=> map_zero _) (fun j a b=> Massive.Patria.Canvas.stylus ..) (fun i b V=>Poised.Plans.Orientation.graphing _ _ _ _ _ (hFt _) _) (fun i j k=>Hom.zero _) hx (fun j hv b=>funext fun U=>by rw [Exposure.eye_value]; exact map_zero _)
    let B(v:Dk):= earnL S ℓ n ℓ Z (fun _=> U) g v; have hX:∀ v:Dk,doubleT A Z (fun _=>U) g V v= - (⇑(B v): Stud _ 6):=by intro v; unfold doubleT; rw [CardsT.receive]; change climbH A ℓ n 0 + _=_; rw [Massive.Lyre.funded_zero _ (hi.trans hv),zero_add]; rfl
    let Y:= (checkedT U (ratioTo S n ℓ) (g P) x); let Y': Stud (S.side R n) 6:= Y
    have he: checkE A ℓ U (g P) (V P) x= -Y':=by
         unfold checkE checkedT; rw [centreN,Massive.Patria.Rolls.roles,Massive.Patria.Rolls.chain_zero]; change climbH A ℓ n 0 - _= _; rw [Massive.Lyre.funded_zero A (hi.trans hv),zero_sub]; rfl
    have hh(k:ℕ)(f:Fin k→ Dk) : (List.ofFn (fun i'=>doubleT A Z (fun _=>U) g V (f i'))).prod=(- (1:ℂ))^k • ⇑(CardsT.rolledT Z (fun _=>U) g k f):=by
         induction k with
         | zero=> unfold CardsT.rolledT; rw [List.ofFn_zero,List.ofFn_zero,pow_zero,one_smul]; rfl
         | succ k ih=> rw [List.ofFn_succ,List.prod_cons,hX,ih (fun i:Fin k=>f i.succ),pow_succ',mul_smul_comm,neg_mul,mul_smul, neg_one_smul,smul_neg]; unfold CardsT.rolledT; rw [List.ofFn_succ (n:=k),List.prod_cons]; rfl
    have hQ:= hh m f; rw [show _= _ from hQ, Massive.Lyre.spend, norm_smul,norm_pow,norm_neg,norm_one,one_pow,one_mul,show checkE A ℓ U _ _ x= _ from he,← neg_one_smul ℂ Y',Massive.Lyre.top_spin,norm_neg,norm_one,one_mul] at hV; exact ⟨m,f,hp',hf,hV⟩
end CardsT
end YM.Intag
#print axioms YM.Intag.CardsT.chamberQ
