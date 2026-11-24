import YM.QCD.Bay.Twig
/-! # Symmetric packages -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Bay
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run Metric Set
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.Local
open Jets Sun Revolve Garden Strut LeafM
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {D V:Type*}[Fintype D][Fintype V][DecidableEq D][DecidableEq V]{f c: Side}{g:D→ Site f}{h:V→Site f}{δ A B t a:ℝ}{m:ℕ}
variable {s:Ratio c f}{P: Therm D s g}{Q:Therm V s h}{G:Grid f→ArrayL D D}{X:Land f D V}{Y:Pays f D D}
lemma roundD (F:Land f D D) : seed (seed F)=F:=by
   funext i j S T; simp only [seed,star_mul,star_star,cT]; have hh : moon (moon T)=T:=by rw [moon,moon]; dsimp only; simp
   rw [hh,← mul_assoc J0 J0,aT,one_mul,mul_assoc,aT,mul_one]
lemma stern {W:Land f D V} (hW:Held s P Q W)(h:Held s P Q X) (c:ℝ): Held s P Q (c • (W+X)):=by
   refine ⟨fun u p T hp U i j S=>?_⟩; simp only [Pi.smul_apply,Pi.add_apply]
   rw [hW.kept u p T hp,h.kept u p T hp]; simp only [driveD,tips,Pi.add_apply, Pi.smul_apply,Matrix.mul_smul, Matrix.smul_mul,Matrix.mul_add,Matrix.add_mul]

lemma carry {F: Land f D D}(h: Pack g g δ t m G A F Y)(ht:Held s P P F)(hr: (fun U=> foldH (G U))=G) : ∃ X Y, Pack g g δ t m G A X Y ∧ Held s P P X ∧ seed X=X:=by
   let K:=seed F
   have hh:= clovering ht; obtain ⟨M,H⟩: ∃ M, Pack g g δ t m G A K M:= ⟨fun i j D=>Y j i D,hr ▸ flock h⟩
   have he:= paid_const (paid_plus h H) ((2:ℝ)⁻¹) (by positivity)
   let X:= (2:ℝ)⁻¹ • (F+K)
   refine ⟨X, (2:ℝ)⁻¹ • (Y+M),?_,stern ht hh _,?_⟩
   · rw [← two_smul ℝ, smul_smul, inv_mul_cancel₀ (by norm_num),one_smul, show (2:ℝ)⁻¹*(A+A)=A from by ring] at he; exact he
   funext i j Z U; simp only [seed,X,Pi.smul_apply,Pi.add_apply,star_smul,star_add,Matrix.mul_smul,Matrix.smul_mul,mul_add,add_mul]; change (2:ℝ)⁻¹ • (_+seed K i j Z U)=_; rw [roundD F]; rw [add_comm]; rfl
-- want G payments

def dot (r : Ratio c f):Therm (Site c) r r.embed:= ⟨Strut.act,podA,fun u i=> (peaks u r i).symm⟩
def sun (r:Ratio c f): Therm (Site f) r id:= ⟨fun p=>act (raise r p),fun u v=>congr_arg act (ups ..)|>.trans (podA ..),fun _ _=>rfl⟩
section
variable {j k p:ℕ}{L:Flight j k}{H:f.val=c.val*L.L.val}
local notation "S"=> sliceL L H
variable {T:Grid f→Sheet f} {A B a t r q:ℝ} {l:ℕ}
structure Sacred (G: Sun L c f H δ a B t r l T) :Prop where
 hearth : Held S (sun S) (sun S) G.X
 hedge : Held S (sun S) (dot S) G.Z
 heels : Held S (dot S) (sun S) G.V
 chiral :seed G.X=G.X
 friendly : seed G.Z=G.V

lemma honoredPack (u:Sun L c f H δ a B t r l T) (hx: Tow S (sun S) (sun S) (inverser T))(hy:(fun U=> foldH (inverser T U))=inverser T)(hz: Tow S (sun S) (dot S) (rightL L H T))
   (hM:(fun U=>foldH (rightL L H T U))=leftL L H T): ∃ V: Sun L c f H δ a B t r l T, Sacred V:=by
   obtain ⟨X,Y,hp,ht⟩:= honors u.X0 hx; obtain ⟨X,Y,hp,hb,hd⟩:= carry hp ht hy; obtain ⟨Z,W,hV,hr⟩:= honors u.Z0 hz; refine ⟨⟨u.positive,u.stable,X,Y,hp,Z,W,hV,seed Z,(fun i j=> W j i),?_⟩,hb,hr,clovering hr,hd,rfl⟩
   exact hM ▸ flock hV
end
end YM.QCD.Bay
