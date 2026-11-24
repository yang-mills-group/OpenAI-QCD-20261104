import YM.Clays.Saga
import YM.Clays.Bonds
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample
open QCD QCD.Grass QCD.Cove Lattice Finset Ribbon Cupola Stew
open Function Lattice Wilson Creek Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph QCD.GasP PhysicalNext.Repeat.Turn Patron Kites Ribbon Cupola Plate Plate.Card Relight Ruby Massive.PCAC
open scoped Topology BigOperators ContDiff Classical Matrix Matrix.Norms.L2Operator
namespace Basal
variable {c:Side}{N:ℕ}{I D:Type}[Fintype I]{a C t b w x v θ m:ℝ}
variable (o:I→Site c)(p:I→Lat.Fields c 6→L[ℂ]Lat.Fields c 6) (H:∀ i,Veins (o i) (p i) C) (s:List I)(d:I→ℂ)
local notation "P"=> Patio (Keys c 6⊕Spine I)
local notation "M"=> ample 6 I
local notation "T"=> traceI I
local notation "Λ"=> Keys c 6
local notation "K"=> actE o p H d s
local notation "Γ"=> effect o p H d
local notation "amt" j:arg=> (s.filter (fun i=> i∈ (j:Finset I)))
variable (F: Reel c 6 I D) {U:BudgetPoint}
set_option quotPrecheck false
local notation "B!"=> U.B
-- W debit formula.Hit.Φ_F.e of E with gap.I.Blue
variable (f:D→Site c)(g:D→ℝ)(h:ValidX o F f g U t)
local notation "E"=> Oper o s F
local notation "Ψ"=> clayR o p H s d F
open ConnectedActivityE6 Blaze King Reserves
variable (hr: ∀ i:I, ‖d i‖≤a)(ha:0≤a)(hC:0 ≤ C)(ht:0<t)(hs:s.Nodup)
include ha hr hC ht hs H h
local notation "ψ"=> extreme o s F g U a C
-- charge on all nonempty including new singles. reach Anchor.Light.By exterior words ∑.
variable (Ft:ℕ) (hf:Fires o Ft)(ε:ℝ)(he:0<ε)(u T':ℝ)(hV:Ac.Hit (fun i=>(F.addr i).support) U.B g (v+2*ε) T')
local notation "A₀"=> absP U.B U.order U.power Ft ε (C*a)*T'
include hV he hf
lemma freshly (hX:hullP U.B Ft*(C*a) ≤ ε) : (Ψ).Occupant o T t U 2 v A₀ (fun _=>1):=by
   let X:=Ψ; have hp:X.Book o T:=booklet o p H s d F _ _ h
   refine ⟨hp,ψ,?_,fun i j hj=>prize o p H s d F _ _ h hr ha hC ht hs i (o j) (hp.stamp i (mem_image_of_mem o hj))⟩; simp only [abs_one,prod_const_one,one_mul]; exact pricing o p H s d F _ _ h hr ha hC ht hs Ft hf ε he T' hV hX
omit hV he hf ha hr hC ht hs H h
local notation "ro"=> rootR (Spine I) Λ
variable (X: Gem c 6 D)
noncomputable def source (I:Type)[Fintype I] : Reel c 6 I D:=⟨X.addr,fun _=>∅,fun i=> (rootR (Spine I) (Keys c 6)) ∘ X.view i⟩
local notation "A!"=> source X I
lemma centers (i:D):Reel.speaker T A! i= light Λ∘ X.view i:=by
     unfold Reel.speaker; funext V; change pluck _ (burst T ∅) (ro _)=_; rw [burst_absent]; exact (revive ..).symm.trans (congr_arg Subtype.val (off ..))
variable (hq:∀ i,shadeG (X.view i))(hW:∀ i,Woven (X.addr i).site (X.addr i).support U t (X.view i) (g i))
local notation "V!" i:arg=> (X.addr i).site
include hq hW ht
lemma pricesY : ValidX o A! (fun i=> V! i) g U t:=by
    refine ⟨fun i=>(X.addr i).anchor,fun i=> ?_,fun i=> (ro).toLinearMap.toContinuousLinearMap.measurable.comp (hW i).Borel,fun i U V h=>congr_arg (ro) ((hW i).room U V h),fun i V=> ?_,fun i V d=>?_,fun i=>?_⟩
    · change (∅:Finset I).image o⊆ _; simp
    · let t:=light _ (X.view i V); refine ⟨show Polite T ∅ (ro (X.view i V)) from ?_,(show clad _ (Ribbon.fiber _ t) from ?_)⟩; rw [Polite,burst_absent]; exact ⟨t,quiet ..⟩
      rw [← quiet]; exact clad.gates _ ((hW i).gated _) _
    · let V':= gauge d V; apply Subtype.ext; change carry _ (slots 6 d).toLinearMap.toContinuousLinearMap (Ribbon.fiber _ _) = Ribbon.fiber _ (X.view i V).val; rw [← quiet,speaks,quiet,show (slots 6 d).toLinearMap.toContinuousLinearMap _= _ from (hq i V d)]; rfl
    rw [centers]; let p:=(light Λ).toLinearMap.toContinuousLinearMap.restrictScalars ℝ; have he:=hW i; refine ⟨fun i U V=>congr_arg p (he.room _ _ V), he.gated, fun i hi=> p.contDiff.contDiffAt.comp 0 (he.use _ hi),fun V hv l hl hp=> ?_,p.measurable.comp he.Borel,he.travel⟩; rw [show leftDerivs (light Λ ∘ X.view i) l V = p _ from left_linear p l (he.use V hv) hl, viewSen _ _ t ht.le]; exact he.pole _ hv l hl hp
omit hq hW ht
lemma lith (I: Type)[Fintype I](V:Grid c)(i:D): Reel.mist (source X I) t i V= rootR (Spine I) (Keys c 6) (letters X t V i):= by
   unfold Reel.mist letters; by_cases h:Healthy t (X.addr i).support V
   · exact (masked_eq _ _ _ _ h).trans (congr_arg (rootR (Spine I) (Keys c 6)) (masked_eq _ _ _ _ h).symm)
   exact (masked_ne _ _ _ _ h).trans ((congr_arg (fun t=> rootR (Spine I) (Keys c 6) t) (masked_ne _ _ _ _ h)).trans (map_zero _) |>.symm)
lemma tip (V:Grid c)(G:Reel c 6 I D)(x:ℝ) (hA:G.Occupant o T t U 2 v x (fun _=>1))(ha:0≤v)(ht:1≤t):Summable fun i=>G.mist U.threshold i V:=by obtain ⟨f,hF,hG⟩:= hA.reserve; simp only [abs_one,prod_const_one,one_mul] at hF; exact creditE o T G f hA.booked hG hF ha ht V
-- anchor fees convert for inputs. World.Q.Encoding. L Growth arithmetic after.
include H hr ha hC ht hs hV he hf
lemma lively (hhS:1 ≤ t)(hv:0 ≤ v)(hF:∀ i, Summable fun j=> Reel.mist F U.threshold j i)(hX:hullP U.B Ft*(C*a)≤ ε)(heX:ValidX o F f g U t) : (Ψ).Occupant o T t U 2 v A₀ (fun _=>1) ∧∀ V:Grid c, K (F.rope U.threshold V)=F.rope U.threshold V+(Ψ).rope U.threshold V:=by
    have hp:= freshly o p H s d F f g heX hr ha hC ht hs Ft hf ε he T' hV hX; refine ⟨hp,fun V=> bountiful o p H s d F f g heX V hs (hF V) (tip o V _ _ hp hv hhS)⟩
omit H hr ha hC ht hs hV he hf
local notation "F'"=> source X I
noncomputable def anth (ε t:ℝ)(B:ℕ):ℝ:= Footprint.payment 1 (4*B+2) 0 ε 1 1 t 0
variable (b' W:ℝ)(hp:Footprint.Anchored (fun i=>(X.addr i).site) g (fun i=> coverNumber U.B (X.addr i).support) b' W)
include hp hW he
lemma roots (b₀:ℝ)(h0:b₀+2*ε≤ b')(hv:0≤b₀):Ac.Hit (fun i=> (X.addr i).support) U.B g b₀ (anth ε b₀ U.B *W):=by
    rw [anth,show _*W=Footprint.payment 1 (4*U.B+2) 0 ε 1 W b₀ 0 from ?_]; swap; · unfold Footprint.payment Footprint.degreeIncome; ring
    have hn(i):0 ≤ g i:=(hW i).travel; refine Footprint.assigned id 1 (fun Y=>by simp) _ _ hn _ _ hp _ _ _ (fun i x p=>?_) (v':=1) (fun i=> by simp) zero_le_one ⟨hv,he,by linarith⟩ g hn (by simp)
    exact (Corona.extent (X.addr i).support U.B p (X.addr i).anchor).trans (by nlinarith)
include ha hr hC hs hq H ht hf
local notation "Ω"=> Oper o s F'
local notation "ΣE"=> clayR o p H s d F'
local notation "Bp!"=> absP U.B U.order U.power Ft ε (C*a)
lemma extracted (hhV: v+4*ε≤ b')(hP':1 ≤ t)(hX:0 ≤ v)(hQ:hullP U.B Ft*(C*a)≤ ε) : (ΣE).Occupant o T t U 2 v (Bp!*(anth ε (v+2*ε) U.B *W)) (fun _=>1)∧∀ V:Grid c,K (ro (Patron.total X U.threshold V))=ro (Patron.total X U.threshold V)+(ΣE).rope U.threshold V:=by
     have H' := roots g ε he X hW b' W hp (v+2*ε) (by linarith) (by linarith); have h(V): Summable (letters X U.threshold V):=Stew.permits _ (⟨g,hp,hW⟩:Licence U b' W t X) ht (by linarith) V
     have hL(V): HasSum (fun i=> (F').mist U.threshold i V) (ro (Patron.total X U.threshold V)) := ((ro).toLinearMap.toContinuousLinearMap.hasSum (h V).hasSum).congr_fun (lith X I V) -- syntax
     obtain ⟨h₁,h₂⟩:=lively o p H s d F' _ g hr ha hC ht hs Ft hf ε he _ H' hP' hX (fun i=> (hL i).summable) hQ (pricesY o g ht X hq hW); exact ⟨h₁,fun V=>by rw [← (hL V).tsum_eq]; exact h₂ V⟩
end Basal
end YM.MassiveQCD.Sample
#print axioms YM.MassiveQCD.Sample.Basal.extracted
