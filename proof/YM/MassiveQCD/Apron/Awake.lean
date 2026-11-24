import YM.MassiveQCD.Stitch.Uniform
import YM.MassiveQCD.Stitch.Rigid
import YM.MassiveQCD.Charter.Paint
import YM.QCD.Calm.Surge
/-! # Extended marker analyticity & shuffling. Compatible at all roots. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Apron
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG Ribbon
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{β τ C μ W:ℝ}
variable {R:Rep su f}{O:BudgetPoint}{F:Tree.Forest S.ratio}{Q:Target su P}{o:Target.Order su W}
variable {H:Cash W τ μ L Q o C T R}{ι κ I E J D:Type}{N:ℕ}
variable (I:Type)[Fintype I] (Y:Fleet H ι N)
local notation "M"=> Ribbon.ample N I
noncomputable def bearing (c:Side)(N:ℕ): EvenA c N→ₐ[ℂ] EvenA c (Ribbon.ample N I):=car (embed (Ribbon.shapeE N I c)) fun x h=> (embed_grade _ x).trans (congr_arg _ h)
local notation "p!"=> bearing I c N
noncomputable def bearer (c:Side)(N:ℕ): EvenA c N→L[ℝ] EvenA c (Ribbon.ample N I):=LinearMap.toContinuousLinearMap ((bearing I c N).toLinearMap.restrictScalars ℝ)
lemma current (x:EvenA c N) : ‖bearing I c N x‖=‖x‖:= Ribbon.scenic (Ribbon.shapeE N I c) x.val
lemma berth (c:Side)(N:ℕ): ‖bearer I c N‖≤1:=by
   refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x=>?_); rw [one_mul]; exact (current I _).le
lemma guide (x:EvenA c N)(a:ℝ): wearK c (Ribbon.ample N I) a (bearing I c N x)=bearing I c N (wearK c N a x):=by
    let F c N:= changeVars (Matrix.diagonal (fun _:Keys c N=>(a:ℂ))); let v:= Ribbon.shapeE N I c; have hp : (embed v).comp (F c N)=(F c M).comp (embed v):=by
       apply ext_atoms; intro i; unfold F; rw [AlgHom.comp_apply, AlgHom.comp_apply, change_atom,embed_atom,change_atom]; simp only [Matrix.diagonal_apply,ite_smul,zero_smul,Fintype.sum_ite_eq,map_smul,embed_atom]
    apply Subtype.ext; exact (DFunLike.congr_fun hp x.val).symm
noncomputable def loommark : Fleet H ι (Ribbon.ample N I) where
 limit:=Y.limit
 ground:=Y.ground
 window:=Y.window
 fine:=Y.fine
 compat:=Y.compat
 works i u v:= bearing I c N (Y.works i u v)
local notation "Z"=> loommark I Y
lemma loping (h:Y.Famous): (Z).Famous:=by
    refine ⟨h.horizons,h.boot,fun i U V W hV=>congr_arg (bearing I c N) (h.locally i U V W hV),fun i U V W hV=> congr_arg (bearing I c N) (h.read i U V W hV),?_, fun i V g hg U=> congr_arg (bearing I c N) (h.roots i V g hg U),h.signs,h.issued⟩
    intro i V; obtain ⟨f,C,hp⟩:=h.pays i V; refine ⟨(bearer I c N).measurable.comp f,C,fun u=>?_⟩; rw [loommark, current]; exact hp _
-- gator only defined trimP? inspect #
lemma lofty (h:∀ i U V,Gated (Y.ground i) (Y.works i U V)) : ∀ i U V,Gated ((Z).ground i) ((Z).works i U V):=by
    intro i U V; refine effects (embed (Ribbon.shapeE N I c)) ?_ _ (h i U V); intro j hj; rw [embed_atom]; apply QCD.Creek.marked; change Ribbon.shape N j I∈_; exact mem_filter.mpr ⟨mem_univ _,by rw [locus]; exact (mem_filter.mp hj).2⟩
lemma larking (h:Colored Y):Colored (Z):=by
    refine ⟨fun z=> ⟨phare _,fun i x y=>?_⟩⟩; apply Subtype.ext; let p:= trade (Lat.rotates N z); have he := (h.warp z).verse i x y
    exact (Ribbon.gaze N z (light _ _) I).trans (congr_arg _ (congr_arg Subtype.val he)) -- inspect
lemma utter (h:Y.speaking): (Z).speaking:=fun i=> (bearer I c N).measurable.comp (h i)
variable {a r e t Λ A:ℝ}{w:ι→ℝ}{p:ι→Site c}{k n m:ℕ}{u:Finset ι}{χ:Chi}
lemma tuck (U:Coat T F)(x)(i): ‖token c (Ribbon.ample N I) a ((Z).coming i U x)‖= ‖token c N a (Y.coming i U x)‖:=by
    have he (u:EvenA c N)(r:ℝ):r • bearing I c N u=bearing I c N (r • u):=(map_smul (bearer I c N) r u).symm
    rw [show (Z).coming _ _ _= bearing I c N (Y.coming i U x) from he ..,skill,guide,current,skill]
lemma gait (h:Y.Theft F p w a t u k n):(Z).Theft F p w a t u k n:=by refine ⟨h.rate,h.grow,h.pack,fun i U hU hu hm z hp=>h.rare i U hU hu hm z (?_), fun i U hU hu hm z=>?_⟩<;> rw [tuck] at *; exact hp; exact h.deck i U hU hu hm z
lemma brush {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{x:E}{f:E→ EvenA c N}{v d:ℝ}(p:Brush k v d f x): Brush k v d (bearing I c N ∘ f) x:=by simpa only [one_mul] using! p.report (bearer I c N) (berth I c N) -- power
lemma high (h:King.Honest Y A Λ t w e a χ m p u k n):King.Honest (Z) A Λ t w e a χ m p u k n:=by
    refine ⟨h.cost,h.yPos,h.age,?_,h.cover⟩; intro F U hU hw hX hy E _ _ _ x V z hV hH i hh; simp only [loommark,guide]; obtain ⟨hp,hG⟩:= h.home F U hU hw hX hy E x V z hV hH i hh; exact ⟨hp.imp_left (fun h=> brush I h),brush I hG⟩
end YM.MassiveQCD.Apron
