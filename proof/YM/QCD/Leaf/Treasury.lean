import YM.QCD.Leaf.Tee
/-! # All links ledger for actual high step -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Leaf.Tee
open Lat Kit Lattice Wilson Finset Function Filter Metric Tree RG Cost
open Orbit Birth Flume Sparks Leaf LeafM Quarry Stationary YM.Next.Free Pine Eyrie Revolve Rudder Garden Run Emblem
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical
variable {c f L:Side}{D: St f}{a b d h r η ξ δ ν A p C R V W E u q e m l G:ℝ}{n j k B x:ℕ}
variable {P:Plan j}{F: Flight j k}{hE:f.val=c.val*F.L.val}{X:Offer 1 a A}{Y:Offer 2 d C}
local notation "Kx"=> trunkM X Y ξ m f
def inverser (D:St f) : St f:= fun i=> (D i)⁻¹
def logs (w:ℝ)(D: St f): St f:=fun i=> lap (zoom w D i)
abbrev markL (S: Flight j k) (h:f.val=c.val*S.L.val):Grid f→Rail c f:=tied S h 0
def foam (F:Flight j k)(h:f.val=c.val*F.L.val)(D: St f):Grid f→Sheet c:=fun U=>1-tied F h 0 U*inverser D U*(tied F h 0 U)ᴴ
abbrev rightL (F:Flight j k)(h:f.val=c.val*F.L.val)(D:St f)(U:Grid f):Rail f c:=inverser D U*(tied F h 0 U)ᴴ
abbrev leftL (F:Flight j k)(h:f.val=c.val*F.L.val)(D:St f)(U:Grid f):Rail c f:=tied F h 0 U *inverser D U
structure Species (F:Flight j k)(hE:f.val=c.val*F.L.val)(v C r b c':ℝ)(B:ℕ)(D:St f):Prop where
 forest : C>0
 reach : v >0
 clump : Own f r b B (logs v D) C
 hashed : Own f r b B (inverser D) C
 soapt : Heritage (sliceL F hE).embed (sliceL F hE).embed r b B (foam F hE D) C
 links : Heritage (sliceL F hE).embed id r b B (leftL F hE D) C
 reigns : Heritage id (sliceL F hE).embed r b B (rightL F hE D) C
 pupils (U): ‖zoom v D U‖ < 1
 crease : ∀ U,Chiral (chirality f) (D U)
 calf : 0<c'
 terrific : ∀ i,Cost.Floor c' (D i)
namespace Species
variable (H:Species F hE V R r b h B D)
include H
lemma sole (U:Grid f): IsUnit (D U).det:= (H.terrific U).unit H.calf
lemma full (U:Grid f): 0<(D U).det.re:=det_pos chi_sq (H.crease U) H.calf (H.terrific U)
lemma trailed (U:Grid f): Real.log (D U).det.re=(∑ i:Site f,(cell (logs V D U) i i).trace.re)-Fintype.card (Row f)*Real.log V:=stamped (D U) (H.crease U) (H.full _) H.reach (H.pupils U)
end Species
lemma planted (P:Plan j)(hb:0≤b)(k:ℕ)(L:Side): ∃ M c v R a:ℝ, 0<M ∧ 0<c ∧ ∃ N:ℕ,∀ B:ℕ,N ≤ B→∀ (X:Flight j k)(hx:X.L=L)(s f:Side)(h:f.val=s.val*X.L.val)(D:St f)(δ:ℝ), 0<δ →δ ≤ c → Own f δ b B D M → (∀ U,Chiral (chirality f) (D U)) → Species X h v R δ b a B (pesto P X h D):=by
  obtain ⟨w,q,g,G,Y,e,M,n,H⟩:=premiere P L k b hb
  obtain ⟨hp,hq,h,hv,hx,hG,hY,he,hm⟩:=H.grades
  let r:=(1-q)/w; have hr:0<r:=by unfold r; exact div_pos (sub_pos.mpr h) hp
  let E:= offer G g; let T:=offerZ w G g; let R:=1+E+T+ Y*T+ (Real.exp b+Y*T*Y)
  have hE:=offer0 hv.le hG.le; have hT:0≤T:=offerZ0 hv.le hG.le hp
  have hR:Real.exp b+Y*T*Y ≤ R:=by unfold R E; nlinarith
  refine ⟨M,e,w,R,r,hm,he,n,fun B hB X hl s f hz D δ ht ha hh hH=>?_⟩
  obtain ⟨hh',h₁,h₂⟩:= H.buy X hl s f hz B hB D δ ht ha hh
  let Q:= pesto P X hz D; let Z:=zoom w Q; have hi i : Cost.Floor r (Q i):=pulseFloor _ hp hq h (h₁ i)
  have hj i : ‖Z i‖<1:=(h₁ i).trans_lt h
  have hr':Own f δ b B (inverser Q) T:=by
    refine Heritage.congregation (T:=fun i=> (w:ℂ) • Z^i) (p:=fun n=>w*(G*g^n)) ht hb (fun i=> ?_) (((summable_geometric_of_lt_one hv.le hx).mul_left G).mul_left w) ?_
    · simpa only [Complex.norm_real, Real.norm_of_nonneg hp.le] using (h₂ i).scalar (w:ℂ)
    intro U; simp_rw [Pi.smul_apply,Pi.pow_apply]; exact Cost.chip _ hp.ne' ((hi U).unit hr) (hj U)
  have he' : Own f δ b B (logs w Q) E:= LapPack h₂ ht hb hv hx hj hG
  have hj': Heritage (sliceL X hz).embed id δ b B (leftL X hz Q) (Y*T):= hh'.1.meet hr' ht hb hY.le hT
  have ht : T≤R:=by unfold R E; linarith only [Real.exp_pos b,hE,hT,show 0 ≤ Y*T by positivity, show 0≤ Y*T*Y by positivity]; -- shadows
  have hh: Y*T ≤ R:=by unfold R E; linarith only [Real.exp_pos b,hE,hT,show 0 ≤ Y*T by positivity, show 0≤ Y*T*Y by positivity]
  refine ⟨lt_of_lt_of_le (by positivity) hR,hp,he'.mono (by unfold R E; linarith only [Real.exp_pos b,hE,hT,show 0 ≤ Y*T by positivity, show 0≤ Y*T*Y by positivity]),hr'.mono ht,?_,hj'.mono hh,(hr'.meet hh'.2 ‹0<δ› hb hT hY.le).mono (by rw [mul_comm]; exact hh),hj, fun U=> unity (ticketStar ..) (hH U),hr,hi⟩
  exact (((Heritage.heritage_one _ hb)).sub (hj'.meet hh'.2 ‹0<δ› hb (by positivity) hY.le)).mono hR
lemma ceremony (ha:0<a)(hd:0<d)(hb:0≤b)(P:Plan j)(k:ℕ)(L:Side)(C A:ℝ):∃ η v R r t:ℝ,0 < t ∧ t ≤ 1 ∧ 0 < η ∧ ∃ N:ℕ,∀ B:ℕ,N ≤B→∀ (X:Offer 1 a A)(Y:Offer 2 d C)(F:Flight j k)(s f:Side)(h:f.val=s.val*F.L.val)(ξ m:ℝ), F.L=L → 0<ξ→ξ≤ t→ |m|≤ t→ Species F h v R (η*ξ^2) b r B (pesto P F h (trunkM X Y ξ m f)):=by
  obtain ⟨δ,T,n,hu,hT,h⟩:=vaultP ha hd hb C A; obtain ⟨M,c,v,R,r,hM,hc,N,H⟩:=planted P hb k L
  let t:=min 1 (M/T/2)
  have he : t ≤ 1:=min_le_left ..
  refine ⟨min δ c,v,R,r,t,lt_min one_pos (by positivity),he,lt_min hu hc,max n N,fun B hB X Y F s f hz ξ m hL hp hx ht=>?_⟩
  have hi:=hx.trans he; let η:= min δ c
  have hη:=lt_min hu hc
  refine H B ((le_max_right ..).trans hB) F hL s f hz _ _ (mul_pos hη (pow_pos hp _)) ((mul_le_of_le_one_right hη.le (pow_le_one₀ hp.le hi)).trans (min_le_right ..)) (((h X Y f B ((le_max_left ..).trans hB) ξ m hp hi).clip (mul_le_mul_of_nonneg_right (min_le_left ..) (by positivity))).mono ?_) (fun i=>tiedStar X Y i ha hd hp hi)
  rw [mul_comm]; apply (le_div_iff₀ hT).1; linarith [show t ≤ M/T/2 from min_le_right ..]
end YM.QCD.Leaf.Tee
