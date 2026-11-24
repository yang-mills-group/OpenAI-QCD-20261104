import YM.QCD.Smoke.Lotus

/-! # M graph transport. Choose costs across all actual and auxiliary forests. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Smoke
open Lat Lattice Wilson Kit Cost Function Finset Tree RG Metric Filter Pine
open Precision Stationary Eyrie Orbit Run Revolve Flume Sparks Quarry Tavern Birth YM.Further.PhysicalPeriodLimitF933 Jacobi Macrame Push.Uniform Garden Transfer
open scoped Matrix Matrix.Norms.L2Operator Topology ContDiff BigOperators Classical
variable {E:Patch} {j k N B:ℕ}{K:KernelChoices}{p:Clip}{r D A u v Λ δ c Y w q g R:ℝ}{M: Before su u v E.J K N}
variable (V: Back E K j k p u v) (J:Plan j)
abbrev anchor (i:ℕ):= act V.fly K V.chain i
abbrev localG (i:ℕ):=high V.fly V.chain i
abbrev quilt (w:ℝ)(T:On)(i:ℕ)(H:Forest (anchor V i).ratio)(t: Bid.Dir su _ → AxisChart su H):= (lap ∘ notch w ∘ shiftH V.fly (divides0 V.fly V.chain i) J (T _) ∘ (fun x:Cnr (V.chain.n i)=> (encamp H t x).1))
-- analytic notch eventually for reps all particular forests via orbit or League
lemma comfort (i:ℕ){H:Forest (anchor V i).ratio}{t:Bid.Dir su _→ AxisChart su H} (h: Critical H p V.path t)
    {U:On} (hh: Vital U)(hp:Arbor J E.L k 1 w q g R δ Y B) :
    ∀ᶠ y:Cnr (V.chain.n i) in 𝓝 0, ‖notch w (shiftH V.fly (divides0 V.fly V.chain i) J (U _) (encamp H t y).1)‖<1:=by
  let X:= fun x:Cnr (V.chain.n i)=>(encamp H t x).1
  have he := (camp_thaw h).1
  have hx : X 0=1:=by unfold X; rw [encamp_zero h]; rfl
  have hM : ContinuousAt (fun x:Cnr (V.chain.n i)=> shiftH V.fly (divides0 V.fly V.chain i) J (U _) (X x)) 0:=(ContinuousAt.add ((canopy ..).continuousAt.comp he.cont) ((mir_ink_sync he hx ((hh.1 _).2.2.2.2)).continuousAt))
  exact (ContinuousAt.norm ((continuousAt_const (y:=1)).sub (hM.const_smul (w:ℂ)))).eventually (gt_mem_nhds (show ‖notch w (shiftH V.fly _ J _ (X 0))‖<1 by
    rw [hx,shiftH,(hh.1 _).2.2.2.1,add_zero]; exact ((hp.uses V.fly V.has (V.chain.n i) (localG V i) _ B le_rfl 0).2.1 1).trans_lt hp.ceil)) -- types
-- INPUT log, EXT. V.path.

def Plume (M:Before su u v E.J K N) (T: On)(r D w : ℝ): Prop:= ∀ i (H:Forest (anchor V i).ratio)(t: Bid.Dir su _ → AxisChart su H),M.Service (S:=anchor V i) H p V.path t → Eyrie.glyph (beam (anchor V i).ratio) Push.Uniform.bolt (Prod.fst (β:=Fiber)) Prod.fst (quilt V J w T i H t) r D
-- natural specialized purchased, bypass-dependent alignment J
lemma speed_cut (M:Before su u v E.J K N) {i j':ℕ} (h:i≤j') (H:Forest (anchor V i).ratio)(t: Bid.Dir su _→AxisChart su H)(hh:M.Service H p V.path t):
    let L:= Lace.project (P:=V.fly.patch) (h:=divides0 V.fly V.chain i) (H:=divides0 V.fly V.chain j') (V.chain.factor i j' h) ((V.port.admiss i).2.2)
    ∃ (G:Forest (anchor V j').ratio) (s:Bid.Dir su _→ AxisChart su G), M.Service G p V.path s ∧ ∀ᶠ x in 𝓝 0,(encamp G s (expandC L.low x)).1=L.high.links (encamp H t x).1:=by
  intro L
  let F : Forest (anchor V j').ratio:= Lace.circuit (P:=V.fly.patch) (H:=divides0 V.fly V.chain j') (V.chain.factor _ _ h) ((V.port.admiss i).2.2) H
  obtain ⟨y,hy⟩:= Before.graph (S:=anchor V j') F M V.port.paid (V.port.admiss j') (congr_arg Patch.J V.origin) rfl
  refine ⟨F,y,hy,?_⟩
  have hz : E.J = V.fly.patch.J:= (congr_arg Patch.J V.origin).symm
  let C:Before su u v V.fly.patch.J K N:=hz ▸ M
  have ht (i j:ℕ)(z:i=j)(M:Before su u v i K N)(h:M.Service (S:=anchor V j') F p V.path y): (z ▸ M: Before su u v j K N).Service (S:=anchor V j') F p V.path y:=by subst j; exact h
  have hc:C.Service F p V.path y:=ht _ _ hz M hy
  exact Quarry.purchased V.fly.patch K _ _ hh.critical hc (Lace.crown ..) (Enrobe.assesses K (V.chain.factor _ _ h) ((V.port.admiss i).2.2) H p V.path)

lemma wind_cut (M:Before su u v E.J K N) {i j':ℕ} (h:i≤j') (H:Forest (anchor V i).ratio)(t: Bid.Dir su _→AxisChart su H)(hh:M.Service H p V.path t)
    (U:On)(hU:Vital U)(hp:Arbor J E.L k 1 w q g R δ Y B) :
    let L:= Lace.project (P:=V.fly.patch) (h:=divides0 V.fly V.chain i) (H:=divides0 V.fly V.chain j') (V.chain.factor i j' h) ((V.port.admiss i).2.2)
    ∃ (F:Forest (anchor V j').ratio) (s:Bid.Dir su _→ AxisChart su F)(d:Site (localG V j')→ℂ),M.Service F p V.path s ∧ Quaint L.high d ∧ ∀ᶠ x in 𝓝 0, quilt V J w U j' F s (expandC L.low x)*stream L.high d=stream L.high d*quilt V J w U i H t x:=by
  intro L
  obtain ⟨F,s,hs,H⟩:= speed_cut V M h H t hh -- F H naming conflict
  obtain ⟨d,hq⟩:= twinkle L.high (bears h) (V.chain.parity i j' h)
  refine ⟨_,_,_,hs,hq,?_⟩
  let A:= expandC L.low; rename_i H'
  filter_upwards [H,comfort V J i hh.critical hU hp, (show Tendsto A (𝓝 0) (𝓝 0) from A.map_zero ▸ A.continuous.continuousAt.tendsto).eventually (comfort V J j' hs.critical hU hp)] with x hx hv hy
  let V' := (encamp H' t x).1
  exact log_stream (p:=d) (show shiftH V.fly _ J (U _) (encamp _ s (A x)).1 * _=stream L.high d * shiftH V.fly _ J (U _) V' from (by rw [show (encamp F s (A x)).1=L.high.links V' from hx]; exact mats_lift V.fly J L _ _ _ hq _ (hU.2 L.high d hq V'))) hy hv -- inspect
end YM.QCD.Smoke
