import YM.Creno.Sill
import YM.Creno.Swath
import YM.Creno.Aero
import YM.Creno.Spoon
/- Ensuring orientations dynamically after reflection without new marker choices. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Acre
open Function Lattice RG Laurent Bloch Matrix Metric Precision Wilson Bid Craft Exterior Filter
open YM.Next.Free YM.Work YM.Further.PhysicalPeriodLimitF933
open WilsonStartup Design Change Extra.Iteration Stationary Tree Raft Garden Transfer Orbit Sparks Fog Birth Raft.ParcelR
open ConnectedActivityE6 Pressure Pressure.Stores
open Push Push.AbsoluteSums Exterior Shell Stationary Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
open PhysicalNext.Repeat Slide PulseRide
open Deck Moss Calm World World.Alley Villa Flume Jets Kit Bay Leaf Tee Run Port Pine Stem Coda Finch Kites Reggae Loom Loom.Fleet Cove Lat
open QCD.Beam Jets.Touch Patron Stem
open Fork GasP Push.Uniform PhysicalNext.Repeat.Song AnalyticBridge.VerifiedReset Time
open scoped PhysicalNext.Repeat.Greenbelt
variable {c f C F L:Side} {J:Patch} {j k n m i l n' :ℕ}{a A d D Y M w x μ q ν η α γ ρ σ η₀ δ ζ H z v u w₀ w₁ w₂ W:ℝ}
variable {P: BudgetPoint}{G:Stage}{T': Teller su}{Q:ConnectedActivityE6.Target su T'}{o:Target.Order su W}
open Stew Ursell
variable {K:KernelChoices}
variable {I J' : Type}
open Blaze Shells Sands Dust King -- edit
open Lapis Sienna Fare Octave Fount Grove
open Planned.JetPort Tidings Entr
open PhysicalNext.JointLoad Heir Warmlet
open Footprint Push.Local Shard DoorKit Badge Adornment
open scoped PhysicalNext.Repeat.Greenbelt
namespace Stratum.MarchQ
open Rails
open ChangeQ Fog.Mist YM.Massive.Stratum
variable {R:BudgetPoint}{χ:Chi}{F₀:Flavor 6}{x W0:ℝ}{st ord:ℕ}
variable {P:SheetR K st ord}{J:(i:ℕ)→Plan (rank i)}
namespace Suburb
variable {gate:ChangeQ→ℕ} {μ tol θ:ℝ} (P₀:Metros P J θ F₀ χ)(A:TrackQ (gate:=gate) P₀)
open Spire.Client (Vows fallback ceilingL fall)
open Track Rails
variable (X:∀ i:ℕ,SlotQ P₀ tol A i) {b:ℝ}
open MeasureTheory Rails.Reference Next.Rank IV Rain
open Finset NormedSpace Grass
open Cairn
open YM.Massive.Pressure (noiseZ)
open YM.SectorNext.Vacuum (rich spare)
variable {κ:ℝ}
open YM.Massive (transfer joint Density Regulator Stiffness.Window Scheme)
open Affair
namespace Melt
open Weft Fibre Sway OrbitG Conductor Conductor.Quant Struck Struck.Library Aperture -- Weft
variable {Pt:ℕ→BudgetPoint}{Δ:PlaqAxes}
variable (B:SparkMesh) (T:Affair P₀ A X B x n) (Z:Sheltered P₀ A X B T k Pt Δ)
set_option quotPrecheck false
local notation "Pq"=> J (A.level i)
local notation "S'"=> T.W.state
local notation "TZ"=> (P.stage (A.level i)).clip
local notation "Kz"=> K
variable (V U W:ℕ→ℝ)(F:∀ i,Pixel (A.ring (B.n k) i) 6)
variable (hp:Tavern P₀ A X B T κ Z V U W F)(hX:entire P₀ A x Pt)(hc:Suburb.Calm P₀ A X x)
variable (E:RiseBook P₀)
open Rails.Kin Massive.Filament
variable (M₀:Arrow 6) {M₃:ℝ} (he:Views P₀ A X E x)
variable (Y:Precinct P₀ A B k n) (hh: Keeps P₀ A X B T V W F Y)
local notation "ζi"=> (clockQ P₀ A x i)
local notation "θ₀"=> θ
local notation "Fz0"=>family P₀ A B Y
local notation "Fz"=>family P₀ A B Y M₀.tip

namespace Lobby
open MassiveQCD.Plate MassiveQCD.Ribbon MassiveQCD.Cupola MassiveQCD.Twist Bank
open Massive.Pressure Rails.Reference.Sharp
-- active point on gears
variable {s w:ℝ}(C:DomeVoice P₀ A X B T V U W E M₀ Y Pt 0 s)
open scoped ComplexOrder
variable (Ht: Uptax P₀ A E x)(O:Paved P₀ A X x) (L1:HaarBudget su)
variable (hC:Glacier P₀ A X B T V U W E M₀ Y Ht C L1 w O)
local notation "DL" hi=> C.Λ i (Nat.zero_le _) hi
local notation "Fz!"=> family P₀ A B Y M₀.tip s
local notation "Tt"=> voyage P₀ A x w i
local notation "cp"=>A.ring (B.n k) i
local notation "fp"=>A.ring (B.n k) (i+1)
variable {Iq AA BB:Type} [Fintype Iq]
-- Mark price route from DomeVoice all.Account property in representation already. Heights regraded goals for firing.
local notation "qS"=> A.spacing i
local notation "sⁱ"=> clockQ P₀ A x i
local notation "x⁺"=> run (A.spacing i) (clockQ P₀ A x i)
local notation "vT"=>fan qS θ sⁱ
local notation "vT₁"=>fan qS θ x⁺
local notation "Dⁱ"=> stepper P₀ A X B T i
local notation "d'T"=>A.next (B.n k) i
local notation "S★"=> (stepper P₀ A X B T i).visit K (A.next (B.n k) i)

open Massive.Poised Massive.Poised.Plans Massive.Poised.Plans.Stamp Tribute Bank.Ontario Massive.Poised.TrainG
variable (Θ:Massive.SourceRead.TaperHol){Vb:YM.Source.Hol su}(Uv:Massive.Lining.Temper.Collage.Exhibit Vb)(i0 Gn :ℕ)(ξ:Fluke Θ Uv Gn)(Ξ:PreLoan Θ Uv i0 P₀ Gn ξ)
local notation "up"=> inflate Θ Uv Gn ξ
local notation "O₁"=> up (Pt (i+1))
local notation "O₂"=> up (Pt i)
variable (hv:BranchPay Θ Uv i0 Gn P₀ ξ Ξ tol (A.node i) (A.flight i) (A.beam i).Θ (A.beam i).c (stanceQ P₀ A i) (A.beam i).fare (X i) (clockQ P₀ A x i))
variable (hL:Gn/2 ≤ (A.node i).lo)(hP1:30*(ξ.r+1) ≤ (A.ring (B.n k) i).val)(htK:TrainG.gateH i0 (run (A.spacing i) (clockQ P₀ A x i)) ≤ (A.ring (B.n k) i).val)
local notation "Tx"=> Massive.transfer (A.flight i) Kz (A.next (B.n k) i) (V (i+1)) (W i)
namespace LifeT.SpinePlan
open Counter Counter.Economies Counter.Tiler
open Massive.Patria Massive.Patria.Depth
open Bank.Hike
local notation "cN"=>A.ring (B.n k)
local notation "Bs"=> being P₀ A X B T V U W E M₀ he Y C Ht O L1 hC Θ Uv i0 Gn ξ Ξ
local notation "Aim"=> covering (n:=n) (k:=k) P₀ A B V U W M₀.tip s w
local notation "Egg"=> egg P₀ A Θ Uv i0 Gn ξ Ξ (Pt:=Pt) (x:=x)
local notation "Fs"=> Kit.slope (A.spacing i)
local notation "Qv"=> ladder P₀ A
local notation "VK"=> Marquee P₀ A X B T V U W E M₀ he Y C Ht O L1 hC Θ Uv Gn ξ
local notation "Zs"=>Massive.Patria.Depth.Bloom Uv Gn
local notation "RH"=> rungs P₀ A (B.n k)
local notation "Un"=> uPulse P₀ A B M₀ Y s w
open MassiveQCD.Sample MassiveQCD.Sample.LoomT MassiveQCD.Sample.Quills
local notation "χS" p:arg=> (Qv).side (B.n k) p
local notation "jσ"=> Blazar.bloom P₀ Θ Uv i0 Gn ξ Ξ
local notation "Wχ"=> FWealth P₀ A Θ Uv Gn ξ (Pt:=Pt) (x:=x)
namespace OrbitK
open Planned.PrimaryIntegral295 Massive.Patria.Depth.Off
namespace Mitos
open Echo Piety Nacre Bounce Talent MassiveQCD.Sample.Eole MassiveQCD.Sample.Eole.Session
namespace Tripos
open PalmX Burd
open Gain MassiveQCD.Sample MassiveQCD.Sample.Kuna MassiveQCD.Sample.Sail
local notation "b₁"=> (Pt (i+1)).B
local notation "qvk"=> (A.spacing i)
local notation "Uℓ"=> salary P₀ A (x:=x)
local notation "Φm" z:arg=>youngF qS z x⁺*(Uℓ (i+1))
variable (Mx:ℝ→ℕ)(Fi Ue:ℕ→ℕ)(Fb Fx Yu:ℕ)(TS0:ℝ)
variable (hCv:Civic P₀ A Θ Uv i0 Gn ξ Ξ Mx Fb Fx Yu TS0 (Pt:=Pt) (i:=i) (x:=x))
open Duop Triple
variable (hi:i+1<n)
variable (hM: Sound (x:=x) P₀ A X Θ Uv i0 Gn ξ Ξ Fi Ue m)(hPz:∀ i,m ≤ i→ i≤ n →30*(ξ.r+1)≤(A.ring (B.n k) i).val)(hGz:∀ i:ℕ,m ≤ i→ i<n→TrainG.gateH i0 (run (A.spacing i) (clockQ P₀ A x i)) ≤ (A.ring (B.n k) i).val)(hYt:SkyQ P₀ A X B T V U W E M₀ Y s C (Nat.zero_le n))(hTol:2*tol+tol^2≤1/2)(hm:m ≤ i)
variable (hAim:(covering (n:=n) (k:=k) P₀ A B V U W M₀.tip s w).Actual)
local notation "Ωv"=> youngF qS (Mx x⁺) x⁺*(Uℓ (i+1))
local notation "GnV"=> (ladder P₀ A).side (B.n k) n
local notation "λX"=> salary P₀ A (x:=x) i
variable (hmY:∀ j,i+1 ≤ j → j ≤ n → 3 ≤ Fi j)(hmH:∀ j,i+1 ≤ j → j < n→1 ≤ Ue j)
variable (sym: Massive.UV.RawSym)(hf:Rubric sym (Bloom Uv Gn))
variable (a:ChangeQ→ℝ)(γ:ℕ→ℝ)(hK:Piety.BudgetL (x:=x) P₀ A X Θ Uv i0 Gn ξ Ξ a m γ)
variable (hGΩ:∀ i:ℕ,m ≤ i→ i≤n→TrainG.gateH i0 (run (A.spacing i) (clockQ P₀ A x i)) ≤ (A.ring (B.n k) i).val)
variable (Q':Massive.Patria.Depth.PatchMix Gn)(hQ: Massive.Patria.Depth.OrderMix (covering (n:=n) (k:=k) P₀ A B V U W M₀.tip s w) Θ sym (Massive.Patria.Depth.Bloom Uv Gn) (i:=m) Q')
local notation "Wz"=>TanK P₀ A X B T V U W E M₀ he Y C Ht O L1 hC Θ Uv i0 Gn ξ Ξ
local notation "Ω"=>Uℓ i
local notation "DΓ"=> Counter.Hymn.damping P₀ A Gn i
local notation "Fn"=> (ladder P₀ A).side (B.n k) n
variable (Ar Ar':Massive.UV.Label Gn)(b:ℕ→ Cover)(q:Bool)(Yp S1 S2 v:ℝ)(hy:Yp>0) (hr:S1>0)(hq:S2>0)
local notation "Fq" x:arg=> comet (Zs) Ar Ar' b Fn n x v
local notation "Tr" X:arg=>trolley Aim X none
variable (hB:Borders (ladder P₀ A) m n b) (hσ:(Pt (i+1)).B*((Pt (i+1)).B) ≤ separation (wrap (A.ring (B.n k) (i+1)) (b (i+1))) 0)(hφ:separation (wrap (A.ring (B.n k) (i+1)) (b (i+1))) 0 ≤ Mx (run (A.spacing i) (clockQ P₀ A x i)))
local notation "Uδ"=> Lobby.Piety.eff P₀ A Θ Uv Gn ξ (x:=x) (Pt:=Pt)
variable (hp1:moored Ar.val q)(hp2:moored Ar'.val false)
variable (hW1:Turf.Floral P₀ A X B T V U W E M₀ he Y C Ht O L1 hC Θ Uv i0 Gn ξ Ξ sym Ar 0 q m (i+1) S1) (hW2:Turf.Floral P₀ A X B T V U W E M₀ he Y C Ht O L1 hC Θ Uv i0 Gn ξ Ξ sym Ar' b false m (i+1) S2)
open Hub
variable (hU: |2*((salary P₀ A (x:=x) i)/Yp*v)| *S1*S2 ≤ (youngF (A.spacing i) (Mx (run (A.spacing i) (clockQ P₀ A x i))) (run (A.spacing i) (clockQ P₀ A x i))*(salary P₀ A (x:=x) (i+1)))^2)
local notation "Gℓ" L:arg p:arg=> Hub.spine sym p L
local notation "Fuelχ" L:arg z:arg=> comet (Zs) (Hub.spine sym Ar L) (Hub.spine sym Ar' L) (Off.sawC b L) GnV n z v
local notation "ZΓ"=> Counter.Hymn.damping P₀ A Gn i
include hp he hh hC hX hc hf hi hTol hM hK hQ hAim hCv hm hmY hmH hPz hGΩ hYt hσ hφ hy hW1 hW2 hU
lemma stencil_p :∃ y:Massive.UV.Label Gn, moored y.val q∧ Tally Θ 0 y ((Aim).density m) ((Tr (fun x=>Fq x)) m 0) ∧ moored (Q' none y).val q∧∃ l, Wχ i l ≤2*Yp ∧ Tally Θ 0 l ((Aim).density i) ((Tr (fun b=> Zs (GnV) b (Q' none y))) i 0):=by
      obtain ⟨p1,h1,h2⟩:=hW1.earns [] (by simp); obtain ⟨p2,h3,h4⟩:=hW2.earns [] (by simp)
      have h:=cannon P₀ A X B T Z V U W F hp hX hc E M₀ he Y hh C Ht O L1 hC Θ Uv i0 Gn ξ Ξ Mx Fi Ue Fb Fx Yu TS0 hCv hi hM hPz hYt hTol hm hAim hmY hmH sym hf a γ hK hGΩ Q' hQ Ar Ar' b q Yp S1 S2 v hy hW1.posK hW2.posK hW2.border hσ hφ hW1.marked hW2.marked p1 p2 h1 h3 h2 h4 hU -- args need order hp1 included & pA .Yes
      obtain ⟨y,h1,hY,h2,p,h3,hP,h4⟩:=h; exact ⟨y,h1,hY,h2,p,h3,hP⟩
omit hp he hh hC hX hc hf hi hTol hM hK hQ hAim hCv hm hmY hmH hPz hGΩ hYt hσ hφ hy hW1 hW2 hU
variable (P0:Massive.UV.Label Gn)
local notation "Cm"=> Q' none P0
local notation "Ct"=> Tripos.berry Gn Cm
local notation "V3"=> Tripos.spare Gn Cm Ar
lemma eyes_berry (L:List Axis): berry Gn (Gℓ L Cm)= berry Gn Cm:=by
     have ht(p:Massive.UV.Label Gn)(L:List Axis):Hub.spine sym p L=0 ↔ p=0:=by induction L with|nil=> rfl|cons a l ih=> rw [Hub.spine]; simp only [map_eq_zero_iff _ ((sym.adj _ a).injective),ih]
     unfold berry; by_cases he:Cm=0; rw [if_pos he, if_pos ((ht ..).2 he)]; rw [if_neg he, if_neg fun hh=>he ((ht ..).1 hh)]
lemma eyes_spare (L:List Axis) : spare Gn (Hub.spine sym Cm L) (Hub.spine sym Ar L)=Hub.spine sym (spare Gn Cm Ar) L:=by
      have ht(p:Massive.UV.Label Gn)(L:List Axis):Hub.spine sym p L=0 ↔ p=0:=by induction L with|nil=>rfl|cons a l ih=> rw [Hub.spine]; simp only [map_eq_zero_iff _ ((sym.adj _ a).injective),ih]
      unfold Tripos.spare; by_cases he:Cm=0; rw [if_pos he, if_pos ((ht ..).2 he)]; rw [if_neg he, if_neg fun hh=>he ((ht ..).1 hh)]
include hp he hh hC hX hc hf hi hTol hM hK hQ hAim hCv hm hmY hmH hPz hGΩ hYt hσ hφ hy hW1 hW2 hU
variable (hℓ:Tally Θ 0 P0 ((covering (n:=n) (k:=k) P₀ A B V U W M₀.tip s w).density m) (trolley (covering (n:=n) (k:=k) P₀ A B V U W M₀.tip s w) (fun X=> Off.comet (Bloom Uv Gn) Ar Ar' b ((ladder P₀ A).side (B.n k) n) n X v) none m 0))
local notation "Ud"=> Lobby.Piety.eff P₀ A Θ Uv Gn ξ (x:=x) (Pt:=Pt)
include hℓ
set_option maxHeartbeats 1300000 in
lemma sous (L:List Axis)(hL:L.length≤8) : let X1:=Hub.spine sym Ar L; let X2:=Hub.spine sym Ar' L; let X3:=Hub.spine sym (Tripos.spare Gn (Q' none P0) Ar) L; let b':= Off.sawC b L
     moored X1.val q∧moored X2.val false ∧ moored X3.val q ∧ (∀ x:Cover, (Ct:ℝ) • Zs (Fn) x X3= Zs Fn x (Q' none (Hub.spine sym P0 L))) ∧∃ p:ℕ→ Massive.UV.Label Gn,p n=X3∧ TanK P₀ A X B T V U W E M₀ he Y C Ht O L1 hC Θ Uv i0 Gn ξ Ξ (p n) q 0 p m ∧ |Ct| * Egg (i+1) (p (i+1)) ≤ ridgeT Θ Uv i0 Gn P₀ ξ Ξ (A.node (i+1)) * (2*Yp*Voyage.tollF P₀ A Θ Uv i0 Gn ξ Ξ i (i+1)) ∧∃ u:ℕ→Massive.UV.Label Gn, u m=0∧(∀ j:ℕ,m ≤ j→j ≤ i →∀ x:Cover, Tally Θ x (u j) (Un j) (FPC P₀ A B (trolley Aim (Tripos.protY P₀ A B Uv Gn (n:=n) (k:=k) X1 X2 X3 (sawC b L) v (-Ct)) none) j x))∧∀ T:ℝ,(1+2*a (A.node i))*Yp ≤ T → ∀ j,m ≤ j→j ≤ i→ Wχ j (u j) ≤ (DΓ j)*T∧ (j < i→ Bounce.wages (fun j=> a (A.node j)) (fun j=> Kit.slope (A.spacing j)) Gn j (Ud j (u (j+1))) (DΓ (j+1)*T) ≤ DΓ j*T):=by
      intro X1 X2 X3 b'
      have hp':i ≤ n:= Nat.le_trans (Nat.le_succ i) hi.le; have ht:= hm.trans hp'; have hx:=Turf.paysV P₀ A X B T V U W E M₀ he Y C Ht O L1 hC Θ Uv i0 Gn ξ Ξ sym Ar 0 q _ hW1 ht
      have he':=Turf.paysV P₀ A X B T V U W E M₀ he Y C Ht O L1 hC Θ Uv i0 Gn ξ Ξ sym Ar' b false _ hW2 ht
      obtain ⟨p1,h1,h2⟩:= hW1.earns L hL; have h0: Off.sawC 0 L=0:= Off.respects _; rw [h0] at h1
      obtain ⟨p2,h3,h4⟩:=hW2.earns L hL; have hp1:= Hub.toured sym Ar q hW1.marked L hx; have hp2:= Hub.toured sym Ar' false hW2.marked L he'
      have hg: separation (wrap fp (b' (i+1))) 0= separation (wrap fp (b (i+1))) 0:=by
           have h:= comparable b (i+1) fp L 0 -- args; edit
           simpa using h
      let P_:= Hub.spine sym P0 L; have h:= cannon P₀ A X B T Z V U W F hp hX hc E M₀ he Y hh C Ht O L1 hC Θ Uv i0 Gn ξ Ξ Mx Fi Ue Fb Fx Yu TS0 hCv hi hM hPz hYt hTol hm hAim hmY hmH sym hf a γ hK hGΩ Q' hQ X1 X2 b' q Yp S1 S2 v hy hW1.posK hW2.posK (Off.bordered b hW2.border L) (hg.symm ▸ hσ) (hg.symm ▸ hφ) hp1.1 hp2.1 p1 p2 h1 h3 h2 h4 hU
      obtain ⟨y,hY,hQm,hY1,l,hl,hV,u,hu,hM',hR⟩:= h
      have hYF:= itinerant P₀ A X B T Z V U W F hp hX hc E M₀ he Y hh C Ht O L1 hC Θ Uv i0 Gn ξ Ξ hTol hPz (fun m h _=>hK.viewQ m h) ht hCv.lo (fun m h _=>hK.vac m h) hGΩ hYt
      have h0 := warms (Aim) Θ sym Zs hf hAim Ar Ar' P0 b hW2.marked v ht (being P₀ A X B T V U W E M₀ he Y C Ht O L1 hC Θ Uv i0 Gn ξ Ξ) hYF L hℓ -- signature order.T ψ
      have hy_:y=P_:= Canvas.consensus _ _ _ hQm _ h0
      have hpP(L:List Axis): Q' none (Hub.spine sym P0 L)= Hub.spine sym Cm L:=by induction L with|nil=>rfl|cons a l ih=> rw[Hub.spine,←hQ.eyeO,ih]; rfl
      obtain ⟨hm1,hm2,px,hKF,hKV,hKP⟩:= gifted P₀ A X B T Z V U W F hp hX hc E M₀ he Y hh C Ht O L1 hC Θ Uv i0 Gn ξ Ξ a γ hK hAim hm hCv.lo hPz hGΩ hYt hTol sym hf q (Q' none y) l X1 Yp hy hi.le hp1.2 hp1.1 hY1 hV hl -- i< n hi.le
      have hd0:Tripos.spare Gn (Q' none y) X1=X3:=by rw[hy_, show Q' none P_= Hub.spine sym Cm L from hpP L]; exact eyes_spare ..
      have heq': Tripos.berry Gn (Q' none y)= Ct:=by rw[hy_, show Q' none P_= _ from hpP L]; exact eyes_berry ..
      rw [hd0] at hm1 hm2 hKF; rw [heq'] at hKP hm2
      refine ⟨hp1.1,hp2.1,hm1,((show y= Hub.spine sym P0 L from hy_) ▸ hm2), px,hKF,hKV,hKP,u,hu,?_,hR⟩
      intro j hj hi' x; let c:= Tripos.protY P₀ A B Uv Gn (n:=n) (k:=k) X1 X2 X3 (sawC b L) v (-Ct);
      have hx : c=((fun x:Cover=>comet Zs X1 X2 b' Fn n x v) - (fun x=> Zs Fn x (Q' none y))):=by
           funext b0; unfold c Tripos.protY; rw [Complex.ofReal_neg,neg_smul,show ((Ct:ℝ):ℂ) • Zs Fn b0 X3= Zs Fn b0 (Q' none y) from hm2 b0, ← sub_eq_add_neg]; rfl
      change Tally Θ x (u j) (Un j) (FPC P₀ A B (trolley Aim c none) j x)
      rw [hx]; exact hM' j hj hi' x
end Tripos
end Mitos
end OrbitK
end LifeT.SpinePlan
end Lobby
end Melt
end Suburb
end Stratum.MarchQ
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.Melt.Lobby.LifeT.SpinePlan.OrbitK.Mitos.Tripos.stencil_p
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.Melt.Lobby.LifeT.SpinePlan.OrbitK.Mitos.Tripos.sous
