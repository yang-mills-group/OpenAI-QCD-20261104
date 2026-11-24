import YM.Differ.Oort
import YM.Differ.Obligato
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG Ribbon Apron Apron.Grove Cupola Plate Card Iris
open MassiveQCD.Sample.LoomT Massive.Poised Massive.Poised.Plans Massive.Poised.Plans.Stamp Massive.UV Stative Massive.Poised.Pipes
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical Stamp
variable {I J E D' :Type}[Fintype I][Fintype J]
open QCD.Kites QCD.Conductor QCD.Acre QCD.Acre.Rails QCD.Struck QCD.Struck.Library Weft
variable {c f L:Side}{v t Θ Γ α β κ:ℝ}{P:BudgetPoint}{k n l m d j:ℕ}
namespace GreenCap.Pavilion
open Kites NormedSpace Stags Sample.Gel Sample.Gel.May Massive.Poised.Plans.Stamp
variable (q:I→Bool)(o:I→ Cover)(H:Massive.SourceRead.TaperHol){U:Source.Hol su}(B:Massive.Lining.Temper.Collage.Exhibit U)(l:I→Label d)(hp:∀ i,moored (l i).val (q i))
local notation "A"=> Keys c 6
local notation "X"=>Patio (A⊕Spine I)
set_option quotPrecheck false
local notation "ow"=>wrap c ∘ o
local notation "Ω"=> loc -- dummy
variable {ν δ ζ:ℝ}(n' j₀ k₀:ℕ) (V₀ B' t:ℝ)(p:BudgetPoint)(he:Pilot H B d p.order p.power n' j₀ k₀ ν δ)(hv:1 ≤ t)(hQ:30*(k₀+1) ≤ c.val)
namespace EntranceW
variable (E:I→Type)[hE:∀ i,Fintype (E i)] (F:∀ i:I,CentreFrame (c:=c) p v (l i) (q i) B (o i) (k₀+1) (E i) Empty)
local notation "G₁" i:arg=> F i
local notation "P₁" i:arg=> ritual (F i)
local notation "S"=> spineV
local notation "Π"=> hQ -- optional
-- weights input=v.Not same outer v! want fan via partial.Core instead abstract v. pert parser.Depends hQ. 
variable (Xc Vc:ℝ)(hPL:∀ i, Published (F i) H n' j₀ (1/8) t Xc 0)(hV:∀ i,Courtesy B (o i) (l i) (q i) p (F i) 4 Vc)
variable (hv':1 ≤ v)
local notation "o†" i:arg =>fun (_:Unit)=> wrap c (o i)
local notation "Yf" i:arg => Puff.stool 6 (wrap c (o i)) (P₁ i) p v (fun _=>∅) (fun _=>1)
local notation "Zf" i:arg=> Stags.baptism 6 (ow) q v i (Yf i)
local notation "M'"=>plume q o B l k₀ p E F -- arg order
variable {E':Type}(e: Patron.Rail c 6 E')(Uq:Patron.Rail c 6 D') (Y:Grid c→ EvenA c 6) (hX:Correspond e Uq)(D:Set (Finset I))(hD:∀ i j,i∈D→j⊆i→j∈D)
open QCD.Ruby Relight
local notation "Wδ"=> momentT q o B l k₀ p E F Uq Y
local notation "Πf"=> (fun i:I=> (Zf i))
local notation "T₀"=>mergeHue (ample 6 I) Πf
local notation "K0"=>bearsZ (J:=I) e
local notation "V₁"=>Trail (T₀) K0 p.threshold
local notation "E0"=>emptyStar (c:=c) I
local notation "XG"=>Roles q B o p d l k₀ F E0
local notation "αT"=> (4:ℝ)
open QCD.Ruby Relight
variable (hvC:0 ≤ Vc) (L₀:ℕ)(hXΦ:Fires (wrap c ∘ o) L₀) (hVC:Stags.bonus L₀ p.B 1*Vc≤1)
variable (L:Side)(x:ℝ)
variable (hS:StackK p.B (taxK L x 4) (taxK L x 2) (3/16) (42/256) (3/16+1) 1) (ht:Pill e p.threshold v p.B (3/16) (taxK L x 4))
variable [Countable E']
variable (Z0:Code c 6) (z0:ℂ)(X0:Grid c→ℝ)(S0:Run.St c)
local notation "Fx"=> Z0.EvalK z0
local notation "ΩH"=> heartS (Z0.EvalE z0) p.threshold X0 S0
variable (θ:ℝ)(hI:v=fan L θ x)(hx: Correspond e (Z0.EvalK z0))(hp₁:Works.OperaBook L L₀ θ Vc x) (hP:p.B=radiusB (run L x))(hs:∀ j∈D,Spaced (wrap c ∘ o) j p.B)
local notation "μ^"=> (taxK L x 1) -- parser alias
local notation "γ"=> roomAt L θ x
include hI hx hV hD he hQ ht hXΦ hp₁ hP hs
lemma struck (hZ:p.threshold=P.threshold)(hPL:∀ i, Published (F i) H n' j₀ (1/8) (taxK L x 1) Xc 0) : PayLayer H B o q p Z0 z0 X0 S0 l (fun _=>Xc) P v (taxK L x 1) (Sail.roomAt L θ x) ((taxK L x ((2-1)/2))⁻¹) (momentT q o B l k₀ p E F Fx ΩH) D n' j₀ (l:=k₀):=by
    obtain ⟨z,C,hz,hC,hx',hf,hXs⟩:= hp₁.costs; let Z:ℂ:= z; have heq:‖Z‖=z:=by unfold Z; rw [Complex.norm_real,Real.norm_of_nonneg hz.le]
    have hT:Z ≠0:= norm_pos_iff.mp (heq.symm ▸ hz); have hZ':Z⁻¹=(↑z⁻¹:ℂ):= (Complex.ofReal_inv _).symm; let XC(i:I):= byG (F i) (↑z⁻¹:ℂ); let k(i):=(↑z⁻¹:ℂ) • l i; have hFi(i:I): Courtesy B (o i) (k i) (q i) p (XC i) 4 C:=by
         have hh: Courtesy B (o i) _ (q i) p (XC i) 4 (‖(↑z⁻¹:ℂ)‖*Vc):= due B (o i) (l i) _ _ (F i) (hV i) (↑z⁻¹:ℂ)
         obtain ⟨f,hV,hp,h₀⟩:= hh.paid; exact ⟨_,hV,hp,h₀.trans ((show ‖(↑z⁻¹:ℂ)‖*Vc=z⁻¹*Vc from by rw [← hZ',norm_inv,heq]).trans_le hx')⟩
    have hNi(i:I): Published (XC i) H n' j₀ (1/8) (taxK L x 1) (z⁻¹*Xc) 0:=by unfold XC; rw [← hZ']; have h:=byGP (F i) (hPL i) Z⁻¹; rwa [mul_zero,norm_inv,heq] at h
    have ht1:1 ≤v:=hI.symm ▸ hp₁.fans -- shadow
    let T:=Sail.roomAt L θ x; let k':= fun i:I=> Z • k i; let F'(i:I):=byG (XC i) Z; let U':=momentT q o B k' k₀ p E F' Fx ΩH
    have hU:= opera q o H B k n' j₀ k₀ p he hQ E XC (z⁻¹*Xc) C hFi ht1 e D hD hC L₀ hXΦ (by rw [hP]; exact hf) L x (hP.symm ▸ hp₁.motion) ht z Z0 z0 X0 S0 hx (fun E' _ Q hvH=> (by rw [hI]; exact hXs c I E' (wrap c ∘ o) q _ _ p hP hXΦ hs (hI ▸ hvH))) T hZ hp₁.holds.le hNi -- sig hp.N.Omit labels h
    -- use h' power scale expression.Weight
    have hY: U'= momentT q o B l k₀ p E F Fx ΩH:=by
          funext i; have he(j:I):plume q o B k' k₀ p E F' j i = plume q o B l k₀ p E F j i:=by
              let g:=plume q o B l k₀ p E F j i; let G:= scaler (Keys c 6) (fun (_:I)=>z); let C':= scaler (Keys c 6) (fun (_:I)=>z⁻¹); have hg : plume q o B k' k₀ p E F' j i=G (C' g):= (scaleLift q o B k k₀ p E XC z j i).trans (congr_arg (scaler ..) (scaleLift q o B l k₀ p E F _ j i))
              rw [hg]; have ht:= (wholeq q o B l k₀ p E F j i).1; change scaler _ _ (scaler _ _ (plume q o B l k₀ p E F j i))= _; rw [stamen A q (fun (_:I)=>z⁻¹) _ _ ht, prod_singleton,map_smul, stamen A q (fun (_:I)=>z) _ _ ht,prod_singleton, ←hZ']; exact inv_smul_smul₀ hT _
          unfold U' momentT; simp_rw [he]
    change PayLayer H B o q p Z0 z0 X0 S0 k' (fun i=>‖Z‖*(z⁻¹*Xc)) P v (taxK L x 1) T ((taxK L x ((2-1)/2))⁻¹) U' D n' j₀ (l:=k₀) at hU
    rw [heq,mul_inv_cancel_left₀ hz.ne',hY,show k'=l from funext (fun i=>by unfold k' k; rw [←hZ']; exact smul_inv_smul₀ hT _)] at hU; exact hU
end EntranceW
end GreenCap.Pavilion
end YM.MassiveQCD.Sample
#print axioms YM.MassiveQCD.Sample.GreenCap.Pavilion.EntranceW.struck
