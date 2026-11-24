import YM.Vest.Ore
import YM.Bank.Spur
import YM.Rebus.Crest
import YM.Hypnos.Tenuous
/-! # Paid one-step primary. COREVS.reducing to payouts
 Geometry over thermal counting stencils includes deterministic Wick-support. Propagating grade.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.TimesV
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG Ribbon Cape Play Play.Chamber QCD.Bera QCD.Anomaly Hypnos Hypnos.Fruit Rot
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
variable {c f L:Side}{J K':Patch}{P:Teller su}{β x C μ W:ℝ}
variable {O:BudgetPoint}{ι κ I Z E D:Type}[Fintype I]
variable {N i j n k m l r t M B Q:ℕ}
open Rebus Matrix Vest
variable (P:Flight j k)(h:f.val=c.val*P.L.val)(K:KernelChoices)
variable (H₀ H₁ :Bed)(A:Towers P.patch.L) -- P.patch namespace?
set_option quotPrecheck false
local notation "ϕ"=> P.visit K h
variable (hu:(curtain su (Flight.visit P K h) H₀ H₁ A).IsSymm)
-- exact ambulatory.
def noteU (I:Type)[Fintype I](N:ℕ):Tone (Kh f) (Dh f N I) (Kh c) (Dh c N I):=⟨Matrix.map (Fruit.view su ϕ H₀ H₁ A) Complex.ofReal,Oce.knock (Fruit.curtain su ϕ H₀ H₁ A) hu,breezeP (Spine I) (Rot.wheelsF N P h),breezeX (Spine I) (Anomaly.stamping (Rot.spider N P h))⟩
def noteV (I:Type)[Fintype I](N r:ℕ):Tone (Kh f) (Dh f N I) (Kh c) (Dh c N I):=⟨raw P h K H₀ H₁ A r,sineP P h K H₀ H₁ A hu r,kpit P h N r I,sfan P h N r I⟩
-- template Telescope endpoints.P
abbrev chalk (c f:Side)(J:Matrix (Exterior.Body 2 f) (Exterior.Body 2 c) ℝ): Matrix (Kh f) (Kh c) ℂ:=(FreeResolvent.tensor su J).map Complex.ofReal
abbrev warpSpin (c f:Side)(X: Kit.Rail f c)(Y: Kit.Rail c f)(I:Type)[Fintype I](N:ℕ):Matrix (Dh f N I) (Dh c N I) ℂ:=breezeP (Spine I) (bladesF (choir N X) (choir N Y))
abbrev chalkW (c:Side)(H:Bed): Matrix (Kh c) (Kh c) ℂ:=(Fruit.coeff su c H).map Complex.ofReal
abbrev warpW (f:Side)(J:Next.Free.Train j)(I:Type)[Fintype I] (N:ℕ) :Matrix (Dh f N I) (Dh f N I) ℂ:= breezeX (Spine I) (stamping (choir N (stage J f)))
variable {Y₀:Bed}{T:Tone (Kh f) (Dh f N I) (Kh c) (Dh c N I)}
-- Canon keeps j twin SPIN and gauge.J NEED NOT SAME! every plateau.F.LOOK.
structure Canon (g r:ℕ)(E H : Bed)(J B:Next.Free.Train r)(T:Tone (Kh f) (Dh f N I) (Kh c) (Dh c N I))(Z: Ratio c f):Prop where
   hue : ∃ X V W, Bank.TowerW g Z E H X V W∧ T.P=chalk c f X
   tilt : ∃ X Y W,QCD.Bank.Giant r Z J B X Y W ∧ T.M=warpSpin c f X Y I N
   berg : chalkW f E= (Matrix.of T.Q.cov)+T.P*chalkW c H*T.P.transpose
   plain : warpW f J I N=T.V+T.M*warpW c B I N*T.M.transpose
open AnalyticBridge.LocalGaussianLaws FreeResolvent
section
-- block algebra
private lemma packA {T U V W: Type}[Fintype T][Fintype U][Fintype V][Fintype W] [DecidableEq W](P: Matrix T U ℂ)(R: Matrix U V ℂ): breezeP W (P*R)=breezeP W P*breezeP W R:=by rw [breezeP,breezeP,breezeP,fromBlocks_multiply]; simp
private lemma packL {T U W: Type}[Fintype T][Fintype U][Fintype W] [DecidableEq W](P:Matrix T U ℂ) (R:Matrix U U ℂ): breezeX W (P*R*P.transpose)=breezeP W P*breezeX W R*(breezeP W P).transpose:=by unfold breezeX breezeP; rw [Matrix.fromBlocks_transpose,Matrix.fromBlocks_multiply,Matrix.fromBlocks_multiply]; simp
private lemma packBar {T U: Type}[Fintype T][Fintype U](P: Matrix T U ℂ)(V:Matrix U T ℂ)(Q:Matrix U U ℂ) : stamping (P*Q*V)=bladesF P V*stamping Q*(bladesF P V).transpose:=by unfold bladesF stamping; rw [fromBlocks_transpose,fromBlocks_multiply,fromBlocks_multiply]; simp
private lemma packed {T U V:Type}[Fintype T][Fintype U][Fintype V] (P:Matrix T U ℂ)(Q: Matrix U T ℂ)(R:Matrix U V ℂ)(S:Matrix V U ℂ) : bladesF (P*R) (S*Q)=bladesF P Q*bladesF R S:=by unfold bladesF; rw [fromBlocks_multiply,transpose_mul]; simp
private lemma lead_add {A: Type}(P Q:Matrix A A ℂ) :stamping (P+Q)=stamping P+stamping Q:=by ext i j; cases i<;>cases j<;> first|rfl |exact (zero_add _).symm
private lemma breA {A W: Type}(P Q: Matrix A A ℂ): breezeX W (P+Q)=breezeX W P+breezeX W Q:=by ext i j; cases i<;> cases j<;> first|rfl| exact (zero_add _).symm
end
-- spin algebra exact
lemma fatherV : stage P.wing f=(father P h)⁻¹ + proton P h*stage P.land c* Garden.barP P h:=by
   let M:= conn P h; let X:= stage P.land c; let U:= stage P.wing f; let G:= father P h
   have he: G= unbarred P.wing f+Mᴴ*M:=rfl; have hv: Garden.barP P h= unbarred P.land c*M*U:=QCD.Bank.father_bar ..
   change U=_; rw [hv, Matrix.mul_assoc (proton P h)]; change U=G⁻¹+G⁻¹*Mᴴ*(X*(unbarred _ _* M*U)); rw [Matrix.mul_assoc (unbarred _ _),← Matrix.mul_assoc X,(links_inv ..).1,Matrix.one_mul]
   conv_lhs=> rw [← Matrix.one_mul U,← G.nonsing_inv_mul (high_rank P h),Matrix.mul_assoc,he,Matrix.add_mul,(links_inv ..).2]; rw [Matrix.mul_add, Matrix.mul_one]; simp only [he,Matrix.mul_assoc]
   simp only [he,Matrix.mul_assoc]
local notation "Te"=> noteU P h K H₀ H₁ A hu I N
-- instance scopes tricky
variable (Z: Flight j j)(d:f.val=c.val*Z.L.val)(V:Towers Z.patch.L)(he:(curtain su (Flight.visit Z K d) H₀ H₁ V).IsSymm)
local notation "Tg"=> noteU Z d K H₀ H₁ V he I N
lemma wheelsSpin : (Tg).M=warpSpin c f (proton Z d) (Garden.barP Z d) I N:=rfl
lemma circleS : warpW f Z.wing I N=(Tg).V+(Tg).M*warpW c Z.land I N*(Tg).M.transpose:=by
     unfold warpW; rw [fatherV Z d]; have hz (P Q: Sheet f): choir N (P+Q)=choir N P+choir N Q:=Matrix.blockDiagonal_add (fun _:Fin N=>P) (fun _:Fin N=>Q)
     rw [hz,lead_add,breA,choir_mul,choir_mul,packBar,packL]; rfl
section gauge
attribute [-instance] Sample.LoomT.instFintypeTo
lemma chalkMul {n:Side}(X:Matrix (Exterior.Body 2 f) (Exterior.Body 2 c) ℝ)(Y:Matrix (Exterior.Body 2 c) (Exterior.Body 2 n) ℝ): chalk n f (X*Y)=chalk c f X*chalk n c Y:=by unfold chalk; rw [AnalyticBridge.LocalGaussianLaws.Current.tensor_mul]; exact Bloch.prom_mul .. -- check namespace
-- establish Real matrix over chosen std inst then transport
lemma circleU : chalkW f H₀= (Fruit.curtain su (Flight.visit Z K d) H₀ H₁ V).map Complex.ofReal+((Fruit.view su (Flight.visit Z K d) H₀ H₁ V).map Complex.ofReal)*chalkW c H₁*((Fruit.view su (Flight.visit Z K d) H₀ H₁ V).map Complex.ofReal).transpose:=by
     unfold chalkW; rw [inverse_f su (Flight.visit Z K d) H₀ H₁ V]; ext; simp [Matrix.mul_apply]
attribute [instance] Sample.LoomT.instFintypeTo
lemma circleG : chalkW f H₀=Matrix.of (Tg).Q.cov+(Tg).P*chalkW c H₁*(Tg).P.transpose:=by
     convert! circleU K H₀ H₁ Z d V using 2 <;> try rfl
     unfold noteU; dsimp only; congr 1 <;> first|congr 2<;> try exact Subsingleton.elim ..|exact Subsingleton.elim ..
end gauge
variable {F0:Clip}{η:ℝ}
lemma Canon.made (ht:Floor H₀ F0 f η C) (hp:Towers.Diagonal (Flight.visit Z K d) H₀ H₁ V): Canon Z.patch.J j H₀ H₁ Z.wing Z.land (Tg) (sliceL Z d) :=⟨⟨_,_,_,Bank.TowerW.single _ _ ht hp,rfl⟩,⟨_,_,_,QCD.Bank.single Z _,rfl⟩,circleG ..,circleS ..⟩
variable {m':Side}{T₀: Tone (Kh c) (Dh c N I) (Kh m') (Dh m' N I)}
variable {r:Ratio c f}{s:Ratio m' c}{D0 D1 D2: Bed}{Jt B Dt : Next.Free.Train j}
-- hue uses Body NORMAL.inst proof (in Bank). need convert.
lemma Canon.series (hp:Canon n j D0 D1 Jt B T r)(he:Canon n j D1 D2 B Dt T₀ s): Canon n j D0 D2 Jt Dt (T.after T₀) (Bank.loom s r):=by
   obtain ⟨⟨M,U,V,h1,hP⟩,⟨E,F,X,h2,hM⟩,hG,hS⟩:=hp
   obtain ⟨⟨M',U',V',h3,h'⟩,⟨E',F',X',h4,hK⟩,hx,hA⟩:=he
   refine ⟨⟨_,_,_,h3.merges h1,?_⟩,⟨_,_,_,h4.next h2,?_⟩,?_,?_⟩
   · unfold Tone.after; dsimp only; rw [hP,h']; convert! (chalkMul M M').symm using 1; congr 1; congr 2; exact Subsingleton.elim ..
   · unfold Tone.after; dsimp only; rw [hM,hK]; unfold warpSpin; rw [choir_mul,choir_mul,packed, packA]
   · rw [hG,hx]; unfold Tone.after; dsimp only; rw [Tone.camped,Tone.scalM]; simp only [Matrix.mul_add,Matrix.add_mul, Matrix.transpose_mul,Matrix.mul_assoc]; abel
   rw [hS,hA]; unfold Tone.after; dsimp only; simp only [Matrix.mul_add,Matrix.add_mul,Matrix.transpose_mul,Matrix.mul_assoc]; abel
private lemma bladeOne {A: Type}[DecidableEq A]: bladesF (1:Matrix A A ℂ) 1=1:=by unfold bladesF; rw [transpose_one]; ext i j; cases i<;> cases j <;> simp [Matrix.one_apply]
private lemma brOne {A T: Type}[DecidableEq A][DecidableEq T]: breezeP T (1:Matrix A A ℂ)=1:=by unfold breezeP; ext i j; cases i<;> cases j<;> simp [Matrix.one_apply]
lemma Canon.unit : Canon n j D0 D0 Jt Jt (Tone.monoT (Kh c) (Dh c N I)) (Bank.idle c):=by
   refine ⟨⟨_,_,_,Bank.TowerW.empty n,?_⟩,⟨_,_,_,QCD.Bank.Giant.unit,?_⟩,?_,?_⟩
   · unfold Tone.monoT; dsimp only; ext ⟨x,p,i⟩ ⟨y,q,j⟩; unfold chalk tensor; simp [Matrix.one_apply]; split_ifs <;> simp_all
   · unfold Tone.monoT; dsimp only; unfold warpSpin breezeP bladesF; ext i j; rcases i with (a|a)|a <;> rcases j with (b|b)|b <;> simp [Matrix.one_apply,replicas]
   · unfold Tone.monoT; dsimp only; rw [show Matrix.of (0:Next.Rank.Normal.Symmetric (Kh c)).cov=0 from rfl]; simp
   unfold Tone.monoT; dsimp only; simp
end YM.MassiveQCD.TimesV

#print axioms YM.MassiveQCD.TimesV.Canon.made
#print axioms YM.MassiveQCD.TimesV.Canon.series
#print axioms YM.MassiveQCD.TimesV.Canon.unit
