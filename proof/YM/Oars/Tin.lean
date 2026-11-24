import YM.Oars.Deduct
import YM.Cardinal.Pockets
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
lemma drift (i:Finset I)(j:Finset J)(u:Patio (Keys c N⊕Spine I))(z:Lat.Frame c)(hv:Melts r P i j)(he:Polite q i u) : parcelColor N z J ((F j) u) = (F j) (parcelColor N z I u):=by
    let p':= (slots N z).toLinearMap.toContinuousLinearMap; let v:= p'; have hg(t:Finset (Spine J))(w:Alg (Keys c N)):(carry (Spine J) v) (stake _ t w)= stake _ t (v w):=speaks S ..
    obtain ⟨a,ha,hZ⟩:=poke M q p (findV r j) g (hym q p r hp j hv.1) i hv.2.1; rw [hv.2.2] at hZ; let Y:=M
    have hw(k:Alg (Keys c N)): (L j) (stake M (burst q i) k)=(a*purse (findV r j) g i) • stake M (burst p j) k:=by
        rw [markedOut,map_mul,hZ,mul_smul_comm,leaves, AlgHom.comp_apply,tarfib,blot_left]; rfl
    apply Subtype.ext; change (carry S v) ((L j) u.val)=(L j) (carry R v u.val); rw [← he.exact, hw, speaks R,map_smul,hg,hw]
lemma tone (V:Lat.Frame c)(i:Finset I)(f: EvenA c (ample N I))(hz: Well N x θ q f)(hf:0<θ) : pick M q i (withdraw N x θ (sways (Lat.rotates (ample N I) V) f))=parcelColor N V I (pick M q i (withdraw N x θ f)):=by
   let P:=withdraw N x θ f; let W:=parcelColor N V I; have hu: withdraw N x θ (sways (Lat.rotates (ample N I) V) f)=parcelColor N V I P:=(congr_arg _ ((congr_arg _ hz.spark.symm).trans ((all_color N x θ q V P hz.applies).symm))).trans (Cupola.home N x θ hf _)
   rw [hu]; apply pluckVisible; intro j; rw [partColor, Cupola.pick,many,many]; split; exact partColor ..; exact (map_zero _).symm
local notation "↑I"=>banknote N x θ
local notation "↑J"=>banknote N y θ
local notation "↓J"=> withdraw N y θ
local notation "↓I"=>withdraw N x θ
local notation "Γ" a=>loft r P a
-- one option incidence in permitted tapes
variable (P₀:I→Support c) (Pt:BudgetPoint)
-- R admits large-faith area T.Campus on all marks. This Sp are used before translations.
noncomputable def tent (Y:Patron.Rail c (ample N I) E)(i:E): Finset (Finset I):= Finset.univ.filter (fun x=>x∈ D∧x⊆ Card.atlas P₀ (Y.addr i).place)
variable (Y:Patron.Rail c (ample N I) E)
-- reuse same index; obtains budget by summing old → ALL chosen repr weighted, no multiplication by volume. Terms personae x∈... only.
noncomputable def loomJ (s:Finset I) (u:T)(i:Finset J) := ↑J ((F i) (pick M q s u))
private def tentX (x:Finset I):= x⊆ univ
noncomputable def tinct (u:Finset I)(X:T): EvenA c (ample N J):=∑ j∈ loft (P:=P) r u, loomJ q p g r N y θ u X j -- order
local notation "K" j => tent (D:=D) N P₀ Y j
noncomputable def castR : Patron.Rail c (ample N J) E:= ⟨Y.addr,fun i V=> ∑ s∈ tent (D:=D) N P₀ Y i, tinct (P:=P) q p g r N y θ s (withdraw N x θ (Y.warp i V))⟩
local notation "Yᴮ"=>castR (D:=D) (P:=P) q p g r N x y θ P₀ Y -- check binder order.N explicitly.$
variable (hY:Wage.Tip N x q Y Pt θ a w)(ht:0<θ)(hq:Gully N x q θ P₀ Y)(hz:∀ i,x i∈ P₀ i)(hv:∀ i j,r i j → y j ∈ P₀ i)
include hY ht
lemma weightB (i:E)(V:Grid c)(s:Finset I)(j:Finset J)(hv: Melts r P s j):(‖Loom.token c (ample N J) θ (loomJ q p g r N y θ s (↓I (Y.warp i V)) j)‖ ≤ ‖purse (findV r j) g s‖ * ‖Loom.token c (ample N I) θ (Y.warp i V)‖):=by
    let X:=pick M q s (↓I (Y.warp i V)); let t:=(F j) X; obtain ⟨hs,c0,hc,hS⟩:= countT M q p g r hp _ _ hv X (choseTuft ..); unfold loomJ; rw [Loom.pulse, show Creek.load _ _=∑ i:Finset (Spine J),load (fun _=>θ) (pluck M i t) from withdrawCost N y θ ht t,sum_eq_single (burst p j),show pluck M (burst p j) t=_ from hS, load_scale,hc]; swap
    · intro b _ hb; rw [show pluck _ b _=0 from hs.spectral b hb,Cove.load_zero]
    rotate_left; · simp
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); have hM: pluck M (burst q s) X= pluck M (burst q s) (↓I (Y.warp i V)):= (many ..).trans (if_pos rfl); rw [hM]; exact (hY.fits ..).pin _ ht
include hq hv
set_option maxHeartbeats 760000 in
lemma building : (Yᴮ).Reg Pt.threshold ∧ (∀ i, shadeG ((Yᴮ).warp i))∧(∀ i V,Well N y θ p ((Yᴮ).warp i V)):=by
    let u (i:E)(k:Finset I)(X:EvenA c (ample N I)):=tinct (P:=P) q p g r N y θ k (↓I X); have h:=hY.tilt.uses
    refine ⟨⟨fun i V K0 he hf=> congr_arg (fun x=>∑ s∈(K i),u i s x) (h.uses i V K0 he hf), fun i=>?_, fun i V=>?_, fun i V hV=> h.buys i V (fun he=>hV (by change ∑ s∈(K i),u i s _=0; unfold u; rw [he,map_zero]; simp only [tinct,loomJ,map_zero,sum_const_zero]))⟩,fun i U k=>?_,fun i V=>?_⟩
    · exact Finset.measurable_fun_sum _ fun s _=> Finset.measurable_fun_sum (f:=fun j V=>loomJ q p g r N y θ s (↓I (Y.warp i V)) j) _ (fun j _=> (↑J).toLinearMap.toContinuousLinearMap.measurable.comp (((F j).toLinearMap.toContinuousLinearMap).measurable.comp ((Cupola.pick M q s).continuous.measurable.comp (((↓I).toLinearMap.toContinuousLinearMap).continuous.measurable.comp (h.reads i))))) -- names maybe 
    · let t:= (Y.addr i).place; let Vx:=↓I (Y.warp i V); change light _ (∑ s∈(K i),u i s _ )∈region (limits t); rw [map_sum]; refine Subalgebra.sum_mem _ (fun j hj=>?_); change light _ (∑ k∈Γ j, loomJ q p g r N y θ j Vx k)∈_; rw [map_sum]; refine Subalgebra.sum_mem _ (fun k hk=>?_)
      have hg:Melts r P j k:=(mem_filter.mp hk).2; obtain ⟨H,c₀,hc,hy⟩:= countT M q p g r hp k j hg (pick M q j Vx) (choseTuft ..); change pen N y θ ((F k) (pick M q j Vx)).val∈_; rw [← H.exact]; apply entitled
      · change pluck M (burst p k) ((F k) (Cupola.pick M q j Vx))∈region (limits t); rw [hy, Cupola.pick,many,if_pos rfl]; exact Subalgebra.smul_mem _ (pennied N x θ _ _ _ (h.role i V)) _
      intro m hm; have hT:m.1.1 ∈ k:= located p _ _ hm; rw [←hg.2.2] at hT; obtain ⟨j₀,hj₀,hk₀⟩:=(frontM _).1 hT; exact (mem_filter.mp ((mem_filter.mp hj).2.2 hj₀)).2 (hv _ _ ((findG r hp.mast _ _ hg.1).1 hk₀).2)
    · let X:=sways (Lat.rotates (ample N J) k); refine congr_arg Subtype.val (?_: X ((Yᴮ).warp i (Lattice.gauge k U))=(Yᴮ).warp i U); change X (∑ s∈(K i),u i s _) =∑ s∈(K i),u i s _; rw [map_sum]; apply sum_congr rfl; intro s hs; unfold u tinct; rw [map_sum]; refine sum_congr rfl fun j hj=>?_
      have hg: Melts r P s j:=(mem_filter.mp hj).2; let v:=Y.warp i (Lattice.gauge k U); let w:=↓I v; let F₀:=(pick M q s w); let t:=(F j); have hF: ↑J (parcelColor N k J (t F₀))= X (↑J (t F₀)):= Cupola.across N y θ p j k _ (countT M q p g r hp _ _ hg F₀ (choseTuft ..)).1; have hl:parcelColor N k J (t F₀) = t (parcelColor N k I F₀):= drift q p g r hp N s j F₀ k hg (choseTuft ..); rw [hl] at hF
      have ht':sways (Lat.rotates (ample N I) k) v=Y.warp i U:= Subtype.ext (hY.tilt.pigment i U k); exact hF.symm.trans (congr_arg (fun e=> ↑J (t e)) ((tone q p r hp N x θ k s v (hY.fits ..) ht).symm.trans (by rw [ht'])))
    change Well _ _ _ _ (∑ s∈(K i),u i s _); refine Well.sum ht _ _ fun s _=> Well.sum (o:=y) ht (Γ s) _ fun j hj=> Mint.launch (Mint.initiate _ ht _ (countT M q p g r hp j s (mem_filter.mp hj).2 _ (choseTuft ..)).1)
end YM.MassiveQCD.Sample
