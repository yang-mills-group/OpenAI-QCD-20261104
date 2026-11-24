import YM.QCD.Coda.Vent
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Coda
open Lattice Wilson Function Finset Filter Metric RG Precision Extra Iteration PhysicalNext.Repeat
open Lat Octave Kit Leaf Tee Port Garden Run Orbit Cove Loom Fleet
open ConnectedActivityE6 Blaze Brush Sienna NormedSpace Lantern Push MeasureTheory Tree
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical
open Reggae Tidings Grass Kites Flume Tee YM.Next.Free Oasis Pressure SectorMeasure Presented
open Jets Beam Villa
variable {n f c:Side}{N j k B B':ℕ}{P:Teller su}
variable {S:Flight j k}{H:f.val=c.val*S.L.val}{w d v u t p C A b m a q β δ:ℝ} {X:Grid f→Sheet f} {W:ℕ→ Atom su 2}
local notation "G"=>sliceL S H
variable {K:KernelChoices}{T:Tube su (Flight.visit S K H)}
local notation "G₀"=>Flight.visit S K H
variable {R:BudgetPoint}{F:Forest (Flight.visit S K H).ratio}
open Token Uniform
set_option maxHeartbeats 490000 in
lemma shear_exp (T:Tube su (Flight.visit S K H))(he:Species S H v u t p b B X) (hg:Own f t p B' (probe v X W) A)(ht:0<t)(hz: Intake P T d (Pane.virgin T R β))(y:Grid c)(hδ:0 < m)(V:EvenA c N)(hp: (G₀).push β (fun U=> (Pane.virgin T R β).eval U • exp (tonic H X W N m U)) y= V) :
   (G₀).push β (Emitter S H K (virginR f N) T δ β 0 R W X) y = (X 1).det^N • Cove.light (Keys c N) (wearK c N m⁻¹ V):=by
   let Q (U:Grid f):=(Pane.virgin T R β).eval U • exp (tonic H X W N m U)
   let L:= ((X 1).det^N • ((Cove.light (Keys c N)).toLinearMap.toContinuousLinearMap.comp ((wearK c N m⁻¹).toLinearMap.toContinuousLinearMap))).restrictScalars ℝ
   have hs : Emitter S H K (virginR f N) T δ β 0 R W X = fun U=> L (Q U):=by
      funext i
      change _=L (Q i); unfold Q; rw [map_smul, gifted T he]; change _•(_ • _) = _ • ((X 1).det^N • Cove.light (Keys c N) (wearK c N m⁻¹ (exp _)))
      rw [NormedSpace.map_exp (wearK c N m⁻¹) (songT (c:=c) (N:=N) m⁻¹).continuous]; exact congr_arg _ (congr_arg _ (congr_arg (Cove.light (Keys c N)) (congr_arg exp (wit _ m⁻¹ m (inv_mul_cancel₀ hδ.ne')).symm)))
   have hr: (G₀).patch.Branches (G₀).kernel su:=hz.ready.knobs.symm ▸ hz.ready.kernel
   have hE : Integrable (fun U=> (G₀).density β U y • Q U) (prior su f):= StepData.push_slice ((G₀).isKernel hr β) y Q (Beam.envDash _ (Env.compact (exp_continuous.comp (portage H X W he hg ht))) _ (((Pane.virgin T R β).envelope hz.cap).integrable _))
   rw [hs]; change _= L V; rw [← hp]; unfold StepData.push; rw [← L.integral_comp_comm hE]; simp only [L, map_smul]
private lemma hex {D E:Type}[MeasurableSpace D][NormedAddCommGroup E][NormedSpace ℝ E][CompleteSpace E] {m:Measure D}{η:D→ℝ}(h:Integrable η m)(x:E):∫ i, η i • x ∂m=(∫ i,η i ∂m) • x :=((1:ℝ→L[ℝ]ℝ).smulRight x).integral_comp_comm h
set_option maxHeartbeats 490000 in
lemma displayK (F: Forest (Flight.visit S K H).ratio)(he:Species S H v u t p b B X) (hg:Own f t p B' (probe v X W) A)(ht:0<t)(hz:Intake P T d (Pane.virgin T R β))
    (y:Positions (Primary c su))(ρ: Positions (Primary c su)→ Poll.Body (Precision.Key F su))(N:ℕ) (hZ:0<tramp T R β y):
    let L:=tonic H X W N m; let f':=L ∘ F.drape; let V:=exp (glimB f' (y,ρ y)); let i:= represent (Uniform.tint su _ y)
    (G₀).push β (fun U=> (Pane.virgin T R β).eval U • exp (tonic H X W N m U)) i= tramp T R β y • (V*(1+Sol («G»:=su) (N:=N) β F T R (Oasis.heat f' ρ) y)):=by
     intro L f' V i; have hr: (G₀).patch.Branches (G₀).kernel su:=hz.ready.knobs.symm ▸ hz.ready.kernel
     have hc: Continuous L:=portage H X W he hg ht; let M:=Pane.virgin T R β; let η:= endoP β F T R y; let Q (U:Grid f):= M.eval U • exp (L U)
     have hp : (G₀).push β Q i=∫ U, η U • exp (f' U) ∂F.order su:=by
        unfold StepData.push; rw [F.pack]; rotate_left
        · exact StepData.push_slice ((G₀).isKernel hr β) i Q (Beam.envDash _ (Env.compact (exp_continuous.comp hc)) _ ((M.envelope hz.cap).integrable _))
        · intro s hS U
          have hS : ∀ i, s ((G).embed i)=1 := hS; have hp : Lattice.gauge (s ∘ (G).embed) i=i:=by funext; simp [Lattice.gauge,hS] -- embed equality defeq
          change _•(M.eval _ • exp _) = _ • (_ • _); rw [show M.eval _= _ from lawful_gi hz.cap s U,show L (Lattice.gauge s U)= _ from brazier he hg U s hS N m,← (G₀).covary hr s β U i]; change _= (G₀).density _ _ (Lattice.gauge (s ∘ (G).embed) _) • _; rw [hp]
        apply integral_congr_ae; filter_upwards with x; rw [show η x= (G₀).density _ _ _ * M.eval _ from Fare.total F T R β i x,mul_smul]; rfl
     have hV := Fare.amt F T R β d P hz i; have he : tramp T R β y=∫ U,η U ∂F.order su:=hV.2
     let z:= tramp T R β y; let W₀:= Oasis.heat f' ρ y; let G' U:=η U • W₀ U
     have hx U: exp (f' U)=V*(1+W₀ U):= by dsimp only [glimB,V,W₀,Oasis.heat]; rw [add_sub_cancel, ← exp_add]; congr 1; abel
     have hn: Integrable G' (F.order su):= Beam.envDash _ (Env.compact (show Continuous W₀ from (exp_continuous.comp ((hc.comp F.continuous_drape).sub continuous_const)).sub continuous_const)) _ (hV.1.integrable _)
     change (G₀).push _ Q i=z • (V*(1+z⁻¹ • (∫ U,G' U ∂F.order su))); rw [hp]; simp_rw [hx,mul_add,mul_one,smul_add ]; -- shape
     let q:=(ContinuousLinearMap.mul ℝ (EvenA c N)) V
     have hW U: η U • (V*W₀ U)= V*G' U:=(q.map_smul (η U) _).symm
     simp_rw [hW]; have hQ: Integrable η (F.order su):=hV.1.integrable _
     rw [integral_add (hQ.smul_const _) (hn.const_mul V),show ∫ a,η a • V ∂F.order su = (∫ a,η a ∂F.order su) • V from hex hQ V]
     rw [← (show z=_ from he)]; apply congr_arg₂ (·+·) rfl
     let u:= ∫ U,G' U ∂F.order su; have hv : ∫ U,V*G' U ∂F.order su=q u:= q.integral_comp_comm hn; rw [hv]
     change q u=z • q (z⁻¹ • u); rw [← q.map_smul,smul_inv_smul₀ hZ.ne'] -- end
end YM.QCD.Coda
