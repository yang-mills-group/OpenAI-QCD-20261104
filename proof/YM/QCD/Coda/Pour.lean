import YM.QCD.Coda.Read
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Shellac.Sables
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Boulevard.Term
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Coda
open Lattice Wilson Function Finset Filter Metric RG Precision Extra Iteration PhysicalNext.Repeat
open Lat Octave Kit Leaf Tee Port Garden Run Orbit Cove Loom Fleet
open ConnectedActivityE6 Blaze Brush Sienna NormedSpace Lantern Push MeasureTheory Tree
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical
open Reggae Tidings Grass Kites Flume Tee YM.Next.Free Oasis Pressure SectorMeasure Presented
open Jets Beam Villa AbsoluteSums Gas Greenbelt Patron Fount Token Uniform GasP Ursell Input
variable {n f c:Side}{N j k B B':ℕ}{P:Teller su}
variable {S:Flight j k}{H:f.val=c.val*S.L.val}{w d v u t p C A b m a q W β θ δ K Ω z η:ℝ}{K':KernelChoices}
local notation "σ"=> Flight.visit S K' H
variable {R R':BudgetPoint}{T:Tube su (Flight.visit S K' H)}
variable {Q:ConnectedActivityE6.Target su P}{o:ConnectedActivityE6.Target.Order su W}
variable {W':ℕ→ Atom su 2}{X:Grid f→ Sheet f}{U':ℝ}
abbrev Vivid (x:Positions (Primary c su)):=represent (Uniform.tint su _ x)
-- preferred potential AUTH ꟻ output priority. galaxy paid via mask.
def oreP (c:Side)(O:Clip)(T: PathData su)(β α π: ℝ)(C:Grid c→EvenA c N)(X D Y:Grid c→Sheet c)(W: ℕ→Atom su 2)(m h:ℝ)(V:Grid c):EvenA c N:= C V+ powerZ c N h (D V)-chalice T O W π Y N h V - m • powerZ c N h (X V)+ baker c N (β*(mainTerm O T V-secondTerm O T V)+(α*secondTerm O T V + Precision.loop T V)) -- D before Y after
variable {s u' ξ:ℝ}
set_option quotPrecheck false
variable (Z: Cash W d v S.L Q o C T (trimP T R δ β 0)) (U:Sun S c f H t u p a b B (houseK s X)){J:Plan k}(Y:Swathe S H (houseK s X) W' J u t a A Ω B') (Γ:Land c (Site c) (Site c))
local notation "V₁"=> tableau S H K' (virginR f N) Z U Y Γ
open scoped PhysicalNext.Repeat.Greenbelt
variable (F:Forest (Flight.visit S K' H).ratio) (D Y':Grid c→Sheet c)(α π:ℝ)(κ:ℕ → Atom su 2)
private lemma rmarks {T:Type*}[NormedAddCommGroup T][NormedSpace ℝ T]{E V T' Y:T}{x d β y:ℝ}{K:ℝ→L[ℝ] T}(hp:E+V+ K (d-β*y)=K x+T'+Y)(Z:T)(M r:ℝ)(u v:T)(a b:ℝ):
     E+V-Z-u+K (β*(M-y)+r) -K (a+b-d)=K (x+β*M+r-a)+(v-Z-K b)+(T'- v - u)+Y:=by rw [show E+V= _ from eq_sub_of_add_eq hp,mul_sub]; simp only [map_add,map_sub]; abel
-- exact on all healthy. for contour too.
set_option maxHeartbeats 490000 in
lemma meteor (χ:Chi) (G: Clusters (V₁).Bright→RegularAddress c) (hZ:∀ i,(G i).support=seatP (V₁).lightF i)(hp: PortD S K' H Z U Y (virginR f N) Γ w m z) (hv:0 < m)(ht:R'.threshold=Pressure.temp d) (hr: Intake P T d (Pane.virgin T R β)) (hB:0<radiusB d)(h:0<t) (ρ:Bid.Dir su c→ AxisChart su F)
    (x:Positions (Primary c su))(hk: 0 < tramp T R β x) (he: flags R'.threshold (Vivid x)=∅) (hQ : ‖((Sol β F T R (Oasis.heat (tonic H (houseK s X) W' N m ∘ F.drape) (Lapis.orbit F ρ)))) x‖ ≤1/2) (hh: ((Fount.favor ρ (tonic H X W' N m) (chalice T.down T.low κ π Y' N m))) 0=baker _ N u') :
   Summable (fun i=> (crude V₁ χ G).view i (Vivid x)) ∧ ((oreP c T.low T.down β α π (wearK c N m ∘ (fun W=>∑' i,(crude V₁ χ G).view i W)) D (Pine.wood J 0 S.land) Y' κ s m)) (Vivid x)-baker c N (harmony T R β α 0 + u'-gala T R Q.table d χ β o.K F)= baker c N (Shellac.off (harmony T R β α) x)+ Shellac.off ((Fount.favor ρ (tonic H X W' N m) (chalice T.down T.low κ π Y' N m))) x+((Fount.amber s m X D S H N W' ρ)) x+bark (((Sol β F T R (Oasis.heat (tonic H (houseK s X) W' N m ∘ F.drape) (Lapis.orbit F ρ)))) x):=by
   obtain ⟨hy,hq⟩:= shearV Z U Y Γ F χ G hZ hp hv ht hr hB h (Lapis.orbit F ρ) x hk he hQ; refine ⟨hy,?_⟩
   let L:= Vivid x; let W₀:= Octave.projection F (x,((Lapis.orbit F ρ)) x)
   let D':= gala T R Q.table d χ β o.K F
   let M:= mainTerm T.low T.down L; let y:=secondTerm T.low T.down L; let r:=α*secondTerm T.low T.down L+Precision.loop T.down L
   let T':= tonic H (houseK s X) W' N m; let E:= wearK c N m (((fun W=>∑' i,(crude V₁ χ G).view i W)) L); let V':= powerZ c N m (Pine.wood J 0 S.land L); let V:= chalice T.down T.low κ π Y' N m L
   let K:=baker c N; let w' :=bark (((Sol β F T R (Oasis.heat (tonic H (houseK s X) W' N m ∘ F.drape) (Lapis.orbit F ρ)))) x); let e:= m
   let R₀:= s • powerZ c N m (D L); change E+V'+ K (D'-β*y)=K (pures T R β x)+T' W₀+w' at hq
   unfold Shellac.off; rw [hh]; let U₀:=tonic H X W' N e W₀
   let j':= harmony T R β α 0; change E+V'-V-R₀+K (β*(M-y)+ r)-K (j'+u'-D')= K (pures T R β x+β*M+r- j')+ (U₀-V-K u')+(T' W₀-U₀-R₀)+w'; exact rmarks hq V M r R₀ U₀ j' _
variable {l:ℕ}{t₁ t₂ t₃ t₄ r₀ d':ℝ}
set_option maxHeartbeats 490000 in
lemma earthP (χ:Chi) (G: Clusters (V₁).Bright→RegularAddress c) (hZ:∀ i,(G i).support=seatP (V₁).lightF i)(hp: PortD S K' H Z U Y (virginR f N) Γ w m z) (hv:0 < m)(ht:R'.threshold=Pressure.temp d) (hr: Intake P T d (Pane.virgin T R β)) (hB:0<radiusB d)(h:0<t) (ρ:Bid.Dir su c→ AxisChart su F)
    (hq:0<t₁)(hh:(Fount.favor ρ (tonic H X W' N m) (chalice T.down T.low κ π Y' N m)) 0=baker _ N u') (he:t₁ ≤1/4) (x:Positions (Primary c su))(hx: (Vivid x)∈Boulevard.sunny R')
     (hK: Brush l t₃ d' (Shellac.off ((Fount.favor ρ (tonic H X W' N m) (chalice T.down T.low κ π Y' N m)))) x)(hM: Brush l t₂ d' (Shellac.off (harmony T R β α)) x) (hα:Brush l t₄ d' ((Fount.amber s m X D S H N W' ρ)) x)
     (hgB: Brush l t₁ d' (Sol β F T R (Oasis.heat (tonic H (houseK s X) W' N m ∘ F.drape) (Lapis.orbit F ρ))) x) (hv':ContinuousAt (Vivid (c:=c)) x) (hX : ∀ᶠ i in 𝓝 x, (Vivid i)∈ Boulevard.sunny R'→ 0 < tramp T R β i ∧ ‖((Sol β F T R (Oasis.heat (tonic H (houseK s X) W' N m ∘ F.drape) (Lapis.orbit F ρ)))) i‖ ≤ t₁) :
     Summable (fun i=> (crude V₁ χ G).view i (Vivid x)) ∧ Brush l (1*t₂+t₃+t₄+feeD l t₁) d' (fun x=> ((oreP c T.low T.down β α π (wearK c N m ∘ (fun W=>∑' i,(crude V₁ χ G).view i W)) D (Pine.wood J 0 S.land) Y' κ s m)) (Vivid x)-baker c N (harmony T R β α 0+u'-gala T R Q.table d χ β o.K F)) x:=by
    refine ⟨(meteor Z U Y Γ F D Y' α π κ χ G hZ hp hv ht hr hB h ρ x (hX.self_of_nhds hx).1 (Boulevard.smoky hx) (hgB.bound.trans (he.trans (by norm_num))) hh).1, ((((hM.report _ (colP c N)).gathering hK).gathering hα).gathering (shelter hq he hgB)).shimmy ?_⟩
    filter_upwards [ (hv'.tendsto.eventually ((Boulevard.sky R').mem_nhds hx)), hX] with i hi hv; exact (meteor Z U Y Γ F D Y' α π κ χ G hZ hp ‹0 < m› ht hr hB h ρ i (hv hi).1 (Boulevard.smoky hi) ((hv hi).2.trans (he.trans (by norm_num))) hh).2
end YM.QCD.Coda
