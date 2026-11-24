import YM.QCD.Coda.Salt
import YM.QCD.Coda.Violet
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Coda
open Lattice Wilson Function Finset Filter Metric RG Precision Extra Iteration PhysicalNext.Repeat
open Lat Octave Kit Leaf Tee Port Garden Run Orbit Cove Loom Fleet
open ConnectedActivityE6 Blaze Brush Sienna NormedSpace Lantern Push MeasureTheory Tree
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical
open Reggae Tidings Grass Kites Flume Tee YM.Next.Free Oasis Pressure SectorMeasure Presented
open Jets Beam Villa AbsoluteSums Gas Greenbelt Patron
variable {n f c:Side}{N j k B B':ℕ}{P:Teller su}
variable {S:Flight j k}{H:f.val=c.val*S.L.val}{w d v u t p C A b m a q W β θ δ K Ω z η:ℝ}{K':KernelChoices}
section derivative
local notation "σ"=> Flight.visit S K' H
variable {R R':BudgetPoint}{T:Tube su (Flight.visit S K' H)}
variable {Q:ConnectedActivityE6.Target su P}{o:ConnectedActivityE6.Target.Order su W} {X:Grid f→Sheet f} {W':ℕ→ Atom su 2}
variable (Z: Cash W d v S.L Q o C T (trimP T R δ β 0)) (U:Sun S c f H t u p a b B X){J:Plan k}(Y:Swathe S H X W' J u t a A Ω B') (Γ:Land c (Site c) (Site c))
set_option quotPrecheck false
local notation "V"=> tableau S H K' (virginR f N) Z U Y Γ
open scoped PhysicalNext.Repeat.Greenbelt
open GasP Ursell Token Uniform Input
lemma tripC (q:ℝ): exp (baker c N q)=Real.exp q • (1:EvenA c N):=by rw [gets]; change exp (sparkF c N (q:ℂ))=_; rw [sky_first,← Complex.ofReal_exp]; rfl
variable (F:Forest (Flight.visit S K' H).ratio)
lemma trade_ink (r m:ℝ) (x y:EvenA c N) (d:Sheet c)(ht:0 < m) (hp : Cove.light _ ((Real.exp r) • exp y)*gauss (Lat.copies N d)=light _ (wearK c N m⁻¹ (exp x))) : exp (wearK c N m y+powerZ c N m d+baker _ N r)= exp x:=by
    let g:= wearK c N m
    have h : exp (y+paleF N d+baker c N r)=wearK c N m⁻¹ (exp x):=by
       apply Port.lit_eqn; rw [exp_add,tripC,exp_add];
       have hh: exp y*exp (paleF N d)*(Real.exp r • 1)= (Real.exp r • exp y)*exp (paleF N d):=by rw [Algebra.mul_smul_comm,Algebra.smul_mul_assoc,mul_one]
       rw [hh,map_mul,light_exp,serviceP]; exact hp
    have he:=congr_arg g h; rw [show g (wearK c N m⁻¹ (exp x))= exp x from wit _ _ _ (mul_inv_cancel₀ ht.ne'), map_exp g (songT (c:=c) (N:=N) m).continuous, map_add,map_add,show g (baker c N r)=_ from juke m r] at he; exact he
lemma beetroot (ρ:Positions (Primary c su)→Poll.Body (Precision.Key F su))(Z:EvenA c N)(hp:‖Z‖≤1/2)(G:F.Slice su→EvenA c N)(u:ℝ)(x:Positions (Primary c su)) :
   Real.exp u • (exp (glimB G (x,ρ x))*(1+Z))=exp (baker _ N u+glimB G (x,ρ x)+bark Z):=by rw [exp_add,exp_add,beech (lt_of_le_of_lt hp (by norm_num)),tripC, Algebra.smul_mul_assoc,one_mul,Algebra.smul_mul_assoc]
lemma coval (x:EvenA c N): indigo c N (wearK c N m x)= indigo c N x:= congr_arg Complex.im (Kites.proofM m x)
lemma bak0 (s:ℝ): indigo c N (baker c N s)=0:=by change (mud _).im=_; rw [gives]; rfl
set_option maxHeartbeats 470000 in
lemma shearV (χ:Chi) (G: Clusters (V).Bright→RegularAddress c) (hZ:∀ i,(G i).support=seatP (V).lightF i)(hp: PortD S K' H Z U Y (virginR f N) Γ w m z) (hv:0 < m)(ht:R'.threshold=Pressure.temp d) (hr: Intake P T d (Pane.virgin T R β)) (hB:0<radiusB d)(h:0<t) (ρ:Positions (Primary c su)→ Poll.Body (Precision.Key F su))(x:Positions (Primary c su))(hk: 0 < tramp T R β x) (he: flags R'.threshold (represent (Uniform.tint su _ x))=∅)
    (hQ : ‖Sol β F T R (Oasis.heat ((tonic H X W' N m) ∘ F.drape) ρ) x‖ ≤1/2):
      let f i:=(crude V χ G).view i (represent (Uniform.tint su _ x)); let I':= Sol β F T R (Oasis.heat (tonic H X W' N m ∘ F.drape) ρ) x; let V':= represent (Uniform.tint su _ x); let g:= tonic H X W' N m ∘ F.drape
      Summable f ∧ wearK c N m (∑' i,f i)+powerZ c N m (Pine.wood J 0 S.land V')+baker c N (gala T R Q.table d χ β o.K F-β*secondTerm T.low T.down V')= baker c N (pures T R β x)+ glimB g (x,ρ x)+bark I' :=by
    intro f' X₁ V' g
    have hh : flags (Pressure.temp d) V'=∅:= ht ▸ he
    let V₀:= V
    have ha := tenet S K' H Z U Y (virginR _ _) χ hp hB
    obtain ⟨hX,hS,hT,hU⟩:= turquoise V₀ χ V' G hZ hh ha
    refine ⟨hS,?_⟩; let r':=gala T R Q.table d χ β o.K F-β*secondTerm T.low T.down V'
    have hp' := (hp.scores χ).2.1 V' F; let u':=(Pane.virgin T R β).eval
    let A:= (X 1).det^N
    let M:= displayK F U.stable (show Own f t a B' (probe u X W') Ω from ⟨Y.walk,Y.coal,Y.att⟩) h hr x ρ N hk (m:=m) -- Own witness
    let D:= Pine.wood J 0 S.land V'; let Z':=pures T R β x
    have hs : tramp T R β x = Real.exp Z':=(Real.exp_log hk).symm
    let Z₁ := exp (baker c N Z'+ glimB g (x,ρ x)+bark X₁)
    have hg : (σ).push β (Emitter S H K' (virginR _ N) T δ β 0 R W' X) V'= A • (Cove.light _ (wearK c N m⁻¹ Z₁)):=by
       apply shear_exp T U.stable (show Own f t a B' (probe u X W') Ω from ⟨Y.walk,Y.coal,Y.att⟩) h hr _ hv; dsimp only at M; rw [M];
       have ht:= beetroot F ρ X₁ hQ g Z' x; change tramp T R β x • _= _; rw [hs]; exact ht
    have h1 := wool T R Q.table d χ V' o.K δ ht he Q.table_exists (show 0 < β from hr.positive) F
    let q:=(crude V₀ χ G); let Q₀:=(∑' i : Clusters V₀.Bright,f' i);
    change _= A • (Cove.light _ (_ • (exp (∑' i,V₀.honest χ V' i)* (∑' i,V₀.ket χ V' i)))*gauss (Lat.copies N D)) at hp'; rw [hX,hT,mul_one,h1, hg] at hp';
    have ht :=trade_ink (c:=c) r' m _ Q₀ D hv (smul_right_injective (Dirac (Modes c N)) (show A≠0 from pow_ne_zero _ (U.stable.sole _|>.ne_zero)) hp'.symm) -- sig
    apply beryl _ _ ht
    · change indigo c N _=0; rw [map_add,map_add,bak0,coval,freed, (show indigo c N (∑' i,f' i)=0 from hU)]; simp
    change |indigo c N _| ≤ _; rw [map_add,map_add,bak0]
    have he : indigo c N (glimB g (x,ρ x))=0:=by
       unfold glimB g; dsimp only [tonic,mica, Function.comp_apply]; rw [map_add (wearK ..), map_add,coval,bak0,zero_add]; exact freed (foam S H X (F.drape (Fare.draw F (represent ((tint su (Exterior.Body 1 c)) x)) (ρ x)))) m
    rw [he, zero_add,zero_add]; apply (indigoF _).trans; refine (sprung hQ (le_refl _)).trans ?_; norm_num
end derivative
end YM.QCD.Coda
