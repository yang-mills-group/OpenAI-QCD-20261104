import YM.Sprig.Litt
/-! Point rotations.Dim.Cost real.Transfer to normalized cofinal contour. -/
set_option autoImplicit false
noncomputable section
namespace YM.Intag.Sprig
open Function Filter MeasureTheory RG Lattice Wilson Cells
open Massive Massive.Patria Massive.Patria.Hub Massive.Patria.Depth Massive.Patria.Rolls QCD QCD.Tide Tarot QCD.Lat QCD.Grass Massive.Patria.Exposure Massive.Lyre Massive.Lyre.Goblet Massive.Romance
open scoped BigOperators ContDiff Topology Classical TensorProduct Matrix.Norms.L2Operator ComplexOrder
variable {C:Sequence} {D d n:ℕ} (P:Calibration C)
open YM.Eden Tarot.Vista CardsT QCD.Acre.Stratum.MarchQ QCD.Acre.Stratum.MarchQ.Suburb QCD.Acre.Stratum.MarchQ.Suburb.Talis QCD.Acre.Stratum.MarchQ.Suburb.Talis.Grammar Sapphire MintV
open Poised Display Plans Sieve Plans.Stamp SourceRead Canvas Ibis QCD.Plum Massive.Elm.SparK.Arbor.Gallery
open UV Massive.Needle Massive.Tarn Massive.Fir YM.Fir.NoteF
namespace Compass
variable (A:Compass C D)
variable (Z:ℕ→ ∀ d,Label d→ₗ[ℂ]Label d)(φ:ℕ→ℕ)(V:∀ d,Label d→ₗ[ℂ] Label d) {β e:ℝ}(ht:C.Path β e)
set_option quotPrecheck false
variable (h:Tendsto φ atTop atTop)(hg: grace (D:=D) Z φ V)(hp:∀ᶠ i in atTop,Plot P A i (Z i))(hA: Known A) (Q:Massive.Tarn.Choir)(hQ:Q.Harmony P φ)
local notation "S"=>Q.total

variable (X: Fin 2→ Glyph D)(hu:∀ i,X i∈A.Ω)(hZ:∀ i,(X i).material≠0)
include ht h hQ hg hp hA hu hZ
open Vale Metric
-- detection throughout fixed analogue region, comparing arbitrary labels at both slots.

omit ht
lemma oxygen {d':ℕ} (L0:Laurel d')(s: RawSym)(J:Landing s L0)(hc:A.e≤ J.e)(hs:J.v≤ A.v)(v:E4)(hv:v∈closedBall J.a J.l) :![0,v]∈ Ibis.flats (Fin 2) (3*A.e) (A.v/4) ∧ ∀ a:Axis,2*A.e ≤ v a:=by
     obtain ⟨he,hv',_⟩:= J.pose _ hv; exact ⟨Ibis.puff _ _ _ he _ _ _ 0 (by rw[sub_self,norm_zero]) (by linarith only [hc]) (by linarith only [hs]),fun i=> le_trans (show _ ≤ 2*J.e from by linarith only [hc]) (hv' i)⟩
include ht
lemma brook {d':ℕ} (L0:Vale.Laurel d')(s: RawSym)(J:Vale.Landing s L0)(hc:A.e≤ J.e)(hs:J.v≤ A.v)(v:E4)(hv:v∈ball J.a J.l): ‖learned A V Q X ![0,v] - candle X (![0,v])‖ ≤ A.bid:=by
     obtain ⟨f,hf⟩:= choicesP P A Z φ V ht h hg hp hA Q hQ X hu hZ hA.hefty v; let F (i:ℕ):Fin 2→ Cover:= ![0,f i]; let K(i):=A.qR (C.N i) (f i); let u(y:E4):Fin 2→ E4:= ![0,y]; let g:=readings P Z X F
     have hm(i:ℕ): A.qR (C.N i) ∘ F i=u (K i):=by ext1 j; fin_cases j; exact digit_zero _; rfl
     have hK: Tendsto (u ∘ K) atTop (𝓝 (u v)):= ((show Continuous u from by unfold u; fun_prop).tendsto v).comp hf
     obtain ⟨hp',hw⟩:= oxygen P A Z φ V h hg hp hA Q hQ X hu hZ L0 s J hc hs v (ball_subset_closedBall hv)
     have hu' : Injective (u v):= noCol _ _ (u v) hp' (by linarith only [hA.live]); have ht' := flight P A Z φ V h hg Q hQ X (u v) F hu' ((hK.comp h).congr fun i=>(hm (φ i)).symm)
     have hX :ContinuousAt (candle X) (u v):= (Ibis.smooth (3*A.e) (A.v/4) X (by linarith only[hA.live]) (u v) hp').continuousAt
     have hT:Tendsto (fun i=> ‖g (φ i)-candle X (u (K (φ i)))‖) atTop (𝓝 ‖learned A V Q X (u v)-candle X (u v)‖):= (ht'.sub ((hX.tendsto.comp hK).comp h)).norm
     apply le_of_tendsto hT; filter_upwards [h.eventually (hf.eventually (Metric.isOpen_ball.mem_nhds hv)), h.eventually hp] with i hi hp1; obtain ⟨hp',hw'⟩:= oxygen P A Z φ V h hg hp hA Q hQ X hu hZ L0 s J hc hs _ (ball_subset_closedBall hi); exact hp1.feast X hu hZ (f _) hp' hw'
omit hu hZ hp hg
structure DiscP (P:Calibration C)(A:Compass C D) (φ:ℕ→ℕ)(V:∀ d,Label d→ₗ[ℂ] Label d)(Q:Choir):Prop where
   legit: Pod P A φ V
   acts : ∀ d,d≤ D→Skin P.sym d (V d)
   book (n:ℕ)(X:Fin n→Glyph D)(hx:∀ i,X i∈A.Ω)(hZ:∀ i,(X i).material≠0)(hk:n ≤ A.K)(x:Fin n→ Cover)(hv:A.qR A.ℓ∘x∈ flats (Fin n) (2*A.e) (A.v/2)): ‖learned A V Q X (A.qR A.ℓ ∘x)- candle X (A.qR A.ℓ ∘ x)‖ ≤ A.bid
   life (n:ℕ)(X:Fin n→ Glyph D)(hx:∀ i,X i∈A.Ω)(hz:∀ i,(X i).material≠0)(hk:n ≤ A.K)(x:Fin n→ E4)(hf:x∈ flats (Fin n) (3*A.e) (A.v/4)): ‖learned A V Q X x‖ ≤ A.dB^n
   homes (X:Fin 2→ Glyph D)(hx:∀ i,X i∈A.Ω)(hz:∀ i,(X i).material≠0)(d:ℕ)(L:Laurel d)(J:Landing P.sym L)(hc:A.e≤ J.e)(hs:J.v≤ A.v)(x:E4)(hv:x∈ball J.a J.l) : ‖learned A V Q X (![0,x])- candle X (![0,x])‖≤ A.bid
lemma depths (F:Pod P A φ V):DiscP P A φ V Q:=by
      obtain ⟨g,Z,h1,hz,hX⟩:=F.proc; let G:=φ∘g; have ht':=h.comp h1.tendsto_atTop; have hQ':=hQ.tuned h1.tendsto_atTop
      exact ⟨F,fun d hd=> outfits P A Z G V ht' hz hX hd,fun n X hu hZ hw x=> stalked P A Z G V ht ht' hz hX hA Q hQ' X hu hZ hw x,fun n X hu hZ hw x=> copper P A Z G V ht ht' hz hX hA Q hQ' X x hu hZ hw, fun X hu hZ d L J hc hs=> brook P A Z G V ht ht' hz hX hA Q hQ' X hu hZ L P.sym J hc hs⟩ -- expected ∀ x
end Compass
end YM.Intag.Sprig
#print axioms YM.Intag.Sprig.Compass.depths
