import YM.Kly.Joice
import YM.Kly.Voices
import YM.Kly.Rapt
set_option maxHeartbeats 520000
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Bridge.Kly
open Function Set Filter Analysis MeasureTheory Measure UV UV.Free
open OS (Cross)
open Fields (pointMoment distinct gram)
open scoped Topology BigOperators InnerProductSpace NNReal ContDiff ComplexOrder Matrix
variable {F:Fields} {S:F.Kernel} {V:Chamber S timeAxis}(P:Spread V)
variable (H:Steady V) (Y:Fields.Euclidean S)(RA:Angular S) {Q:Sequence}{C:Calibration Q}(E:F.System C){B:Bases F}{M':Momentum F}(U:B.Content C M')
variable (x:F.W)(w:P.algebra→⋆ₐ[ℂ]ℂ)(hx:Continuous w)
local notation "Sα"=>bloom P H w
local notation "t₀"=>timeAxis
open OS.Ground (Panes)
open TopologicalSpace Chamber
variable (h:∀ x:F.W,F.adj t₀ (F.parity x)= F.parity (F.adj t₀ x))(hR:∀ i:Axis,∃ p:EuPin,Leads F i p)(hW:Physics.Ward M' S)(hs:Fruits S)
-- only requires Φ comparison on all pure characters of chamber time
include P E H Y RA h hR hW hs U
lemma pledges (hΦ:∀ X' :P.algebra →⋆ₐ[ℂ] ℂ,Continuous X'→B.Comparison (bloom P H X')) : ∃ p:Vacua F,p.Decomposes S M' B :=by
      obtain ⟨A,hA,hc⟩:= Kly.ascent P H Y RA E h
      have hy(i:A.X):Fields.Euclidean (bloom P H (A.character i)):= qualified P H Y RA E U _ (hA.values i) (hΦ _ (hA.values i)) h hR
      have ht:= picks P H Y E U A hA hy; haveI:IsProbabilityMeasure A.μ:= hA.normalized
      obtain ⟨p,hp⟩:= ht.exists; obtain ⟨T,hT⟩:= mintP (V:=V) E hs; obtain ⟨f,hf⟩:= elephant P T hT A hA
      let v:Vacua F:= { X:=A.X, μ:=A.μ, flavor:=f, ensemble:=fun i=> bloom P H (A.character i), chosen:=p }
      have he{n:ℕ} (x:Points n)(hx:x∈ conf n)(u:Fin n→F.W) :Continuous fun i:A.X=> v.ensemble i n x u:= hA.weak _
      refine ⟨v,hA.normalized,fun x hx H'=>?_,hy,fun n x hx=> he x hx, ?_,fun n x hx u=>(he x hx u).integrable_of_hasCompactSupport (μ:=A.μ) (HasCompactSupport.of_compactSpace _),fun x=> hΦ _ (hA.values x),fun x=> yieldU P H Y RA E (A.character x) (hA.values x) h M' hW, stroll P H Y E T hT A hA f hf,fun x=> passports P H Y E T hT A hA hc f hf x,?_,ht,hp⟩ -- order
      · have:= hA.support -- need install
        change 0<A.μ x; exact pos_iff_ne_zero.mpr (hA.support.open_pos x hx H') -- name
      · intro n x hx u
        let z:Cluster F:=realize u x; have hz:distinct z:=(realized ..).2 hx; rw [show (∫ i,v.ensemble i n x u ∂v.μ)=∫ i,A.character i (M P z hz) ∂A.μ from congr_arg (fun f:A.X→ℂ=> ∫ i,f i ∂A.μ) (funext fun i=> poll P H x u (A.character i) hx), ← readAt, hA.ground]; obtain ⟨s,d,H'⟩:=Spread.place_exists hz; change pointMoment S z= inner ℂ V.omega0 _; change _= inner ℂ V.omega0 ((M P z hz).val V.omega0); rw[overline P H _ _ s H', P.insertValue _ _ _, invariance Y hz]
      intro n x hx u p i; let z:=realize u x; let w:= bank p (⟨_, (show distinct z from (realized ..).2 hx)⟩:Pack F); have hy :realize (F.flavor p ∘ u) x= w.val:=by change _=List.map _ _; unfold z realize; rw [List.map_ofFn]; rfl
      change (bloom P H (A.character (f p i))) n x _=(bloom P H (A.character i)) n x u; rw[poll _ _ x _ _ hx,poll _ _ x _ _ hx]; have hm : M P (realize (F.flavor p ∘ u) x) ((realized ..).2 hx)= M₀ P w:=by unfold M₀; congr 1 -- defeq
      rw[hm]; exact reacts P H Y E T hT A hA f hf p i (⟨z, (realized ..).2 hx⟩)
end YM.Massive.Bridge.Kly
#print axioms YM.Massive.Bridge.Kly.pledges
