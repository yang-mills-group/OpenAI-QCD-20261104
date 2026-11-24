import YM.Oars.Tin
import YM.VMarker.Totes
/-! # Renderer motion on same flags; no data tier chosen again inside hierarchy.V: -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample
open QCD QCD.Grass QCD.Cove Lattice Finset Ribbon Cupola
open Function Lattice Wilson Creek Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph QCD.GasP PhysicalNext.Repeat.Turn Patron Kites Ribbon Cupola Plate Plate.Card Relight Ruby
open scoped Topology BigOperators ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {A B C I J E :Type}[Fintype A][Fintype B][Fintype C][Fintype I][Fintype J]
variable (A) (q:I→Bool)(p:J→Bool)(f:I→Option J)(g:I→J→ℝ)
local notation "R"=>Spine I
local notation "S"=>Spine J
local notation "Z"=> A⊕R
variable (r:I→J→Prop) {P:Set (Finset J)} {D:Set (Finset I)}(hp:Pledge q p r P D) {c:Side}{N:ℕ} {a b w:ℝ}(x:I→Site c)(y:J→Site c) (θ:ℝ)
-- preservation of unary arc. All-color, pin.Carry, puncture invariance
include hp
local notation "M"=>Keys c N
local notation "T"=> Patio (M⊕R)
local notation "L" j=>leaves M q p (findV r j) g
local notation "F" j=>flame M q p (findV r j) g -- notation conflicts.f implicit
variable (N)
local notation "↑I"=>banknote N x θ
local notation "↑J"=>banknote N y θ
local notation "↓J"=> withdraw N y θ
local notation "↓I"=>withdraw N x θ
local notation "Γ" a=>loft r P a
variable (P₀:I→Support c) (Pt:BudgetPoint)
variable (Y:Patron.Rail c (ample N I) E)
local notation "K" j => tent (D:=D) N P₀ Y j
local notation "Yᴮ"=>castR (D:=D) (P:=P) q p g r N x y θ P₀ Y -- check binder order.N explicitly.$
variable (hY:Wage.Tip N x q Y Pt θ a w)(ht:0<θ)(hq:Gully N x q θ P₀ Y)(hz:∀ i,x i∈ P₀ i)(hv:∀ i j,r i j → y j ∈ P₀ i)
namespace Recolor
include ht hp hY hq hv hz
open ConnectedActivityE6 Pressure
omit hY hv hz
section lit
local notation "Lι" i=> shutter M i
-- whole projection needs old D hereditary (proof). on each bit where becomes feasible.
lemma turnT (i:E)(j:Finset J)(V:Grid c)(hb:j∈P): (Lι j) (↓J ((Yᴮ).warp i V))=(F j) (↓I (Y.warp i V)):=by
    let u:=K i; let Z':=↓I (Y.warp i V); let Xq:=F j; let G:=fun s:Finset I=>Xq (Cupola.pick M q s Z')
    change (Lι j) (↓J (∑ s ∈u,tinct ..) )=_; rw [map_sum,map_sum] -- definability K issues
    refine Eq.trans (b:=∑ s∈u,G s) ?_ ?_
    · refine sum_congr rfl fun k hk=>?_ ; unfold tinct; rw [map_sum]; let X:=Cupola.pick M q k Z'; have h(s:Finset J): ↓J (loomJ q p g r N y θ k Z' s)=(F s) X:= Cupola.home N y θ ht _; change (Lι j) (∑ t∈_,↓J (loomJ q p g r N y θ k Z' t))=_; simp_rw [h]; exact fareSum M q p g r hp hb _ _ (choseTuft ..)
    let W:=Card.atlas P₀ (Y.addr i).place; have hm: Z'= ∑ a∈ (Finset.univ.filter (fun a=> a ∈ (W.powerset:Set (Finset I)))), Cupola.pick M q a Z' :=(hq.vfs ..).wholeV
    nth_rw 1 [show ↓I _= _ from hm]; rw [map_sum]; refine sum_subset (fun k hk=>mem_filter.mpr ⟨mem_univ _,mem_powerset.mpr ((mem_filter.mp hk).2.2)⟩) fun k hk h=>?_ -- `nth_rw` nested LHS
    exact portR _ _ _ g r hp k _ _ hb (choseTuft ..) (fun hh=>h (mem_filter.mpr ⟨mem_univ _,hh, mem_powerset.mp ((mem_filter.mp hk).2)⟩)) -- order
lemma slide (i:E)(V:Grid c): vacR S M (↓J ((Yᴮ).warp i V))=vacR R M (↓I (Y.warp i V)):=by
    apply Subtype.ext; let X:= (↓I (Y.warp i V)); let S':= (F (∅:Finset J)); let A:= (↓J ((Yᴮ).warp i V)); let Q:=(shutter M (∅:Finset J))
    change resetM S M _= resetM R M _; rw [revive,revive]; change pluck M ∅ A=pluck M ∅ X
    have h':Q A=S' X:=turnT q p g r hp N x y θ P₀ Y ht hq i ∅ V hp.mast.empty
    have hm:pluck M ∅ (Q A)=pluck M ∅ A:=by unfold Q shutter; rw [Cupola.pulse]; simp [Cupola.pole]
    refine hm.symm.trans ((congr_arg (pluck M ∅) h').trans ?_)
    have hW:X= ∑ a∈ (Finset.univ.filter (fun a=> a∈((atlas P₀ (Y.addr i).place).powerset:Set (Finset I)))), Cupola.pick M q a X:=(hq.vfs i V).wholeV;
    -- compute all nonempty killed; empty unchanged-body
    rw [hW,map_sum,map_sum,map_sum]; refine sum_congr rfl fun j hj=>?_; let p':=Cupola.pick M q j X; have ht': Polite q j p':=choseTuft ..
    by_cases ht:j=∅
    · subst j; unfold Cupola.pick; rw [burst_absent]
      let Zκ:= chooseBlade M ∅ X; change scrape M ∅ ((L (∅:Finset J)) (Zκ).val)=scrape M ∅ (Zκ).val; change scrape M ∅ ((L (∅:Finset J)) (stake M ∅ (pluck M ∅ X))) = scrape M ∅ (stake M ∅ (pluck M ∅ X)); rw [quiet,leaves, AlgHom.comp_apply,tarfib,blot_left,← quiet, ← quiet,quid,quid]
    have hx : ¬ Fare (findV r ∅) j:=fun h=> Exists.elim (nonempty_iff_ne_empty.mpr ht) fun z hj=> h.2 z hj (by simp [findV]); change pluck M ∅ (S' p')= _; rw [show S' p'=0 from latentF M q p _ g (hym q p r hp (∅:Finset J) hp.mast.empty) _ _ ht' hx,map_zero]; exact (ht'.spectral _ (fun h=>ht ((burstUnique q ((burst_absent q).trans h)).symm))).symm
lemma faultSeat : faultK N y θ Yᴮ=faultK N x θ Y :=by
    let h(u v:Patron.Rail c N E)(hp:u.addr=v.addr)(hh:u.warp=v.warp):u=v:=by cases u; cases v; congr
    exact h _ _ rfl (funext fun i=>funext fun V=>slide q p g r hp N x y θ P₀ Y ht hq i V)
include hY
variable (v:ℝ)(heD:∀ i j, i∈D→j⊆i→j∈D) (h:1 ≤ θ)(hA:0≤a)(hw:1≤w)(U:Type)(Ft:Patron.Rail c N U)(hU:Correspond (faultK N x θ Y) Ft)
local notation "Fᵢ"=> Film.publication N x q Y D θ
local notation "Rᵢ" Y=> Film.publication N y p Y P θ
variable (V:Grid c)
include heD hU h hw hA
-- vintage when mapping output. Needs old validPh on both reports and true Rail
omit hU
lemma integral {A w':ℝ} (hb:Wage.Tip N y p (castR (D:=D) (P:=P) q p g r N x y θ P₀ Y) Pt θ A w')(hA':0 ≤ A)(hw':1 ≤ w') (i: Finset J)(hx:i∈P): (Lι i) (↓J (heartK Yᴮ Pt.threshold V))=(F i) (↓I (heartK Y Pt.threshold V)):=by
    let Y':= Yᴮ; let U:= (F i).comp (↓I); let S':=(Lι i).comp (↓J); unfold Kites.heartK; change S'.toLinearMap.toContinuousLinearMap (_) = U.toLinearMap.toContinuousLinearMap _; rw [ContinuousLinearMap.map_tsum _ (profits Y' V h hw' hb.tilt.sold hA' _), ContinuousLinearMap.map_tsum _ (profits Y V h hw hY.tilt.sold hA _)]; apply tsum_congr; intro u
    change S' (tK Y' _ V u)= U (tK Y _ V u); unfold tK; split
    next h0=> rw [if_pos (show separated (blocked (Ruby.home Y)) u ∧ flags Pt.threshold V=u.biUnion (oriD Y) from h0),map_prod,map_prod]; exact prod_congr rfl fun k hk=>turnT q p g r hp N x y θ P₀ Y ht hq k i V hx -- arguments
    next h0=> rw [if_neg (show ¬(separated (blocked (Ruby.home Y)) u ∧ flags Pt.threshold V=u.biUnion (oriD Y)) from h0),map_zero,map_zero]
lemma cool (i':Finset J)(hz:i'∈P)(K₁:Type)(Zκ:Patron.Rail c N K₁)(hc:Correspond (faultK N x θ Y) Zκ): (F i') (Film.reports N Fᵢ Zκ Pt.threshold V)= (F i') (↓I (heartK Y Pt.threshold V)):=by
   let v := Film.reports N Fᵢ Zκ Pt.threshold V; let u := ↓I (heartK Y Pt.threshold V); let Wv:=ValidPieces M q (Finset.univ:Finset I);
   have hΦ:Wv v:=by
       let p':=Film.addressSets N Fᵢ Zκ; let fG j:=Film.spruced N Fᵢ Zκ j V; let f(i:Finset _):=Plate.roof p' fG (flags Pt.threshold V) i
       have hX:Summable (fun i=>‖fG i‖):=Summable.sum _ (Film.payable (rootR R M).toLinearMap.toContinuousLinearMap (hc.coins V)) (Film.seat_norm N x -- x collision. rename
           q θ Y D V (prints Y V hY.tilt.uses hY.tilt.sold hw hA h))
       apply ValidPieces.tab (rum p' _ _ hX).hasSum; intro i
       change Wv (f i); unfold f Plate.roof; split; next _=> exact Subalgebra.prod_mem (ValidPieces.course (A:=M) q Finset.univ) (fun u _=>by
                    rcases u with u|u; swap; · exact ValidPieces.role (u.snd.val) (choseTuft ..) (subset_univ _)
                    apply ValidPieces.role ∅ _ (empty_subset _); unfold Polite; rw [burst_absent]; exact ⟨_,quiet ..⟩ ) -- indent
       exact ValidPieces.noneV
   have hP: Well N x θ q (heartK Y Pt.threshold V):=by
       apply Well.total ht; intro i; unfold Ruby.tK; split
       · exact Well.product _ _ (fun i _=> hY.fits ..)
       exact Well.zeroV
   let t:= F i'; have hf:= hP.applies; have htU:u= ∑ i∈ Finset.univ.filter (fun z=> z∈ ((Finset.univ:Finset I).powerset:Set (Finset I))),Cupola.pick M q i u:=hf.wholeV; change t v= t u
   rw [hΦ.wholeV,htU,map_sum,map_sum]; refine sum_congr rfl fun i hi=>?_; by_cases H:i∈D; swap; · rw [show t _=_ from portR M q p g r hp i i' _ hz (choseTuft M q i v) H, show t _=_ from portR M q p g r hp i i' _ hz (choseTuft M q i u) H];
   have hKv: shutter M i v=shutter M i u:= Film.mergeFront N x q θ Zκ Y D i (fun j hv=>heD i j H (mem_powerset.mp hv)) hY.fits ht hY.tilt.uses hc V (prints Y V hY.tilt.uses hY.tilt.sold hw hA h)
   apply congr_arg t; apply Subtype.ext; exact congr_arg (stake M (burst q i)) (phoenixC M v u i hKv (burst q i) (located q i)) -- binder fun
end lit
end Recolor
end YM.MassiveQCD.Sample
