import YM.Pollen.Pennies
import YM.Pollen.Acts
import YM.MassiveQCD.Cupola.Wood
import YM.MassiveQCD.Stitch.Mint
set_option autoImplicit false
noncomputable section
namespace YM.Massive.PCAC
open QCD QCD.Grass QCD.Lat Lattice Wilson RG Function Filter MeasureTheory QCD.Grass.Ward
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator Classical
variable {c f:Side}{n N j k F:ℕ}
open Onsite Tide QCD.Cove Creek
open Finset
open MassiveQCD MassiveQCD.Ribbon MassiveQCD.Cupola
variable {C:ℝ}{I:Type}[Fintype I]
variable {p:Lat.Fields c N→L[ℂ]Lat.Fields c N}(H: Bean p) 
local notation "X"=> Keys c N
local notation "S"=> Spine I
local notation "P" => Patio (Keys c N⊕Spine I)
local notation "B!"=> burst (traceI I)
local notation "T"=>Stitch.Tablet.credits
local notation "M"=> ample N I
open QCD.Loom
include H
set_option maxHeartbeats 660000 in
lemma shone (a:ℂ)(i:I)(x:P){t:ℝ}(ht:0<t)(hv:∀ x:Fields c N, load (fun _=>t) (p x)≤ C*load (fun _=>t) x) : T t (H.dies a i x) ≤ ‖a‖*(C*T t x):=by
     let y:= H.twirl I x; let q':= Stitch.Tablet.chip t X S; have hz:T t y≤C*T t x:=by
           change load (expRate (p:=fun _=>t) (q:=fun _=>1)) (light (X⊕S) y) ≤ C*load (expRate (p:= fun _=>t) (q:=fun _=>1)) (light (X⊕S) x); let f (x: P)(i:Finset S):=load (fun _=>t) (pluck X i x); rw [fiscal (p:=fun _=>t) (q:=fun _=>1) (fun _=> ht) (fun _=>one_pos), fiscal (p:=fun _=>t) (q:=fun _=>1) (fun _=>ht) (fun _=>one_pos),mul_sum]; simp only [prod_const_one,one_mul]; exact sum_le_sum fun j _=> (show f y j≤ C*f x j from (Eq.trans_le (congr_arg (load (A:=X) (fun _=>t)) (show pluck X j y=_ from Bean.onPiece I H ..)) (hv _))) -- not rfl need wing.
     have he : T t (echoI X i)=1:= Eq.trans (Stitch.Tablet.polite_bill {i} (echoI X i) (itOwn i) ht) (by rw [show scrape X (B! {i}) (echoI X i).val=1 from quid ..]; exact Cove.load_one _)
     rw [Bean.fate]; change load q' (light _ (a • _)) ≤ _; rw [map_smul, load_scale]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); rw [map_mul]; exact (load_mul ..).trans (show T t (echoI X i)*T t y≤ _ from (congr_arg (fun t=> t*T _ y) he).trans_le ((one_mul _).trans_le hz))
omit H
open Further.DenseMixedKernels
variable (a:ℂ)(i:I) {V:Grid c→Lat.Fields c N→L[ℂ]Lat.Fields c N}{v:Site c}{U:BudgetPoint}
-- embed price steering B height. needed generic lane.T
structure Suit (o: Site c) (Point:BudgetPoint)(A:ℝ)(v:Grid c→Lat.Fields c N→L[ℂ]Lat.Fields c N) :Prop where
    bean x: Bean (v x)
    haloS : Lattice.LocalOn (halo 1 {o}) v
    gauge x g y : v x (slots N g y)=slots N g (v (Lattice.gauge g x) y)
    bloc x (Y:Support c):∀ y:Fields c N, y∈region (limits Y) → v x y ∈ region (limits (Y∪ halo 1 {o}))
    empty x (Y:Support c): o∉Y→∀ y:Fields c N,y∈region (limits Y)→ v x y=0
    law x y: ber _ (v x y)=0
    nng:0≤ A
    lanes : ∃ (J:Type)(_ : Fintype J)(s:J→Lat.Fields c N→L[ℂ]Lat.Fields c N)(f:J→Grid c→ℂ)(w d:J→ℝ), ∑ i,w i*d i ≤ A ∧ (∀ i,Bean (s i)∧0 ≤ d i∧0 ≤w i ∧Continuous (f i)∧ (∀ U (p:Site c), Pitch (f i) U (Point.dirBound p) Point.order (w i) ((1+(separation o p:ℝ))^Point.power)) ∧ (∀ t,0<t→∀ x, load (fun _=>t) (s i x) ≤d i*load (fun _=>t) x)) ∧ ∀ U,v U=∑ i,f i U • s i
variable (h:Suit v U C V)
include h
namespace Suit
set_option quotPrecheck false
local notation:max "Ω" j:arg=> (h.bean j).dies a i
local notation "F!"=> V
private lemma sumV' (x:Grid c)(J:Type)[Fintype J] (s:J→Lat.Fields c N→L[ℂ]Lat.Fields c N)(f:J→Grid c→ℂ)(hd :∀ k,Bean (s k))(hv:∀ U:Grid c,F! U=∑ i,f i U • s i) (y:P): Ω x y= ∑ j, f j x • ((hd j).dies a i y):=by
    have he:(h.bean x).twirl I y=∑ j, f j x • (hd j).twirl I y:=by
         apply pluckVisible; intro t; rw [Bean.onPiece,map_sum]; simp_rw [map_smul,Bean.onPiece]; rw [hv]; simp
    simp_rw [Bean.fate,he,mul_sum,smul_sum,mul_smul_comm]; exact sum_congr rfl fun i hi=> smul_comm ..
lemma holes (x y:Grid c)(hp:Agrees (halo 1 {v}) x y) : Ω x = Ω y:=by
    have hu:= h.haloS x y hp; let f:= V x; let g:=V y; suffices h:∀ g (hg:Bean g) (R:f=g), (h.bean x).dies a i=hg.dies a i by exact h g _ hu -- syntax arg .?
    rintro _ _ rfl; rfl
lemma dyes (x:Grid c)(g: Frame c)(y:P): parcelColor N g I (Ω (Lattice.gauge g x) y)= Ω x (parcelColor N g I y):=by
    rw [Bean.fate,Bean.fate,map_smul,map_mul,echoColor]; apply congr_arg; apply congr_arg; apply pluckVisible; intro j; rw [Bean.onPiece,partColor,partColor,Bean.onPiece,h.gauge]
lemma stakes (x:Grid c)(Y:Support c)(y:P)(hp:clad (limits Y) y.val) : clad (limits (Y∪ halo 1 {v})) (Ω x y).val:=((clad.gates _ ((region _).one_mem) _).mul (reCarry _ _ _ (fun y hz=>h.bloc x Y y hz) _ hp)).scale a -- infer
lemma expires(x:Grid c)(Y:Support c)(y:P)(he:v∉Y)(hp:clad (limits Y) y.val): Ω x y=0:=by
    rw [Bean.fate,show (h.bean x).twirl I y=0 from ?_,mul_zero,smul_zero]
    apply pluckVisible; intro i; rw [Bean.onPiece,map_zero]; exact h.empty _ _ he _ (hp _)
-- meas for arbitrary near
lemma spends {D:Grid c→P}(he:Measurable D): Measurable (fun x=> Ω x (D x)):=by
    obtain ⟨Q,hQ,F,G,R,w,hV,hh,hp⟩:= h.lanes; simp_rw [sumV' a i h _ Q _ _ (fun i=>(hh i).1) hp]; exact Finset.measurable_sum _ fun i _=> Measurable.smul ((hh i).2.2.2.1.measurable) ((((hh i).1).dies a _).measurable.comp he) -- edit name
lemma spendsC {D:Grid c→P}(he:Continuous D): Continuous (fun x=> Ω x (D x)):=by
    obtain ⟨Q,hQ,F,G,R,w,hV,hh,hp⟩:= h.lanes; simp_rw [sumV' a i h _ Q _ _ (fun i=>(hh i).1) hp]; exact continuous_finsetSum _ fun i _=>(hh i).2.2.2.1.smul ((((hh i).1).dies a _).continuous.comp he)
lemma post {D:Grid c→P}(x:Grid c){r b u:ℝ}(hr:0<r)(o:Site c) (hp: Phy r D x (U.dirBound o) U.order b u)(he:0 ≤ u) : Phy r (fun t=> Ω t (D t)) x (U.dirBound o) U.order (‖a‖ * C*b) ((1+(separation v o:ℝ))^U.power+u):=by
    obtain ⟨Q,hQ,F,G,R,w,hV,hh,hg⟩:= h.lanes; let m:ℝ:=‖a‖; let p:= (1+(separation v o:ℝ))^U.power; have hm:0≤ m:=norm_nonneg _; have hP:0≤ p+u:= add_nonneg (by unfold p; positivity) he
    let f(i':Q)(V:Grid c):= G i' V • ((hh i').1.dies a i (D V)); let g(i:Q):=m*(R i*w i)*b; have hF(i'): Phy r (f i') x (U.dirBound o) U.order (g i') (p+u):=by
        obtain ⟨hξ,h₀,hY,hU,hX,hW⟩:=hh i'; have hv:=hp.linear (hξ.dies a i) (fun z=> (shone hξ a _ z hr (hW r hr)).trans_eq (mul_assoc ..|>.symm)) (mul_nonneg hm h₀)
        unfold g; rw [show m*(R i'*w i')*b=R i'*(m*w i'*b) from by ring]; exact Phy.prod hv (hX x o) -- order
    have hw':=Phy.ton (t:=r) univ f g hP (fun i _=>hF i); rw [show (fun t=> Ω t (D t))=∑ i', f i' from funext fun y=> Eq.trans (sumV' a i h y Q _ _ (fun i=>(hh i).1) hg _) (by simp [f])]; refine hw'.more ?_ hP le_rfl; unfold g; rw [←sum_mul,←mul_sum]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hV hm) hp.nn
lemma bills (x:Grid c){r:ℝ}(hr:0<r)(p:P): Stitch.Tablet.credits r (Ω x p) ≤ ‖a‖*C*T r p:=by
   have h:= post a i h x hr v (Phy.fixedX p (by norm_num:(0:ℝ)≤0)) le_rfl
   simpa only [leftDerivs,List.length_nil,pow_zero,mul_one] using! h.paid [] (Nat.zero_le _) (by simp)
end Suit
end YM.Massive.PCAC
#print axioms YM.Massive.PCAC.Suit.bills
#print axioms YM.Massive.PCAC.Suit.stakes
