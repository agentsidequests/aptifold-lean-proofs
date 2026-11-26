"""Render numbered paper figures and a 5:2 X cover from checked result records."""

import json
import math
from pathlib import Path
import re
import sys

import numpy as np
from reportlab.lib.colors import HexColor, Color, white
from reportlab.pdfgen.canvas import Canvas


OUT = Path(__file__).resolve().parent / "figures"
DATA = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).resolve().parent / "data"
INK = "#102D36"
BLUE = "#176786"
TEAL = "#156B55"
RUST = "#A24923"
MUTED = "#465C64"
LINE = "#C9D9DD"
PALE = "#EDF5F4"
PAPER = "#FFFFFF"


def color(c):
    return HexColor(c)


def label(c, x, y, text, size=13, tone=INK, bold=False, anchor="left"):
    c.setFillColor(color(tone))
    c.setFont("Helvetica-Bold" if bold else "Helvetica", size)
    write = {"left": c.drawString, "center": c.drawCentredString, "right": c.drawRightString}
    write[anchor](x, y, text)


def lines(c, x, y, text, size=13, gap=18, tone=INK, bold=False):
    for index, row in enumerate(text):
        label(c, x, y-index*gap, row, size, tone, bold)


def rect(c, x, y, w, h, fill=PALE, stroke=None):
    c.setFillColor(color(fill))
    c.setStrokeColor(color(stroke or fill))
    c.rect(x, y, w, h, fill=1, stroke=int(stroke is not None))


def path(c, points, tone=INK, width=1.4, dash=None):
    if len(points) < 2:
        return
    c.setStrokeColor(color(tone))
    c.setLineWidth(width)
    c.setDash(dash or [])
    p = c.beginPath()
    p.moveTo(*points[0])
    for point in points[1:]:
        p.lineTo(*point)
    c.drawPath(p, stroke=1)
    c.setDash([])


def dot(c, x, y, tone, r=4, hollow=False):
    c.setFillColor(white if hollow else color(tone))
    c.setStrokeColor(color(tone))
    c.setLineWidth(1.8)
    c.circle(x, y, r, stroke=1, fill=1)


def arrow(c, start, end, tone=TEAL):
    path(c, [start, end], tone, 1.1)
    a = math.atan2(end[1]-start[1], end[0]-start[0])
    corners = [(end[0]-7*math.cos(a+t), end[1]-7*math.sin(a+t)) for t in (-.45, .45)]
    path(c, [corners[0], end, corners[1]], tone, 1.1)


def canvas(name, title, sub, height=330):
    c = Canvas(str(OUT / (name+".pdf")), pagesize=(720, height), pageCompression=1)
    c.setTitle(title)
    rect(c, 0, 0, 720, height, PAPER)
    label(c, 22, height-30, title, 23, INK, True)
    label(c, 22, height-50, sub, 11.6, MUTED)
    path(c, [(22, height-61),(698, height-61)], LINE, 1)
    return c


def axes(c, box, limits, xticks, yticks, xname, yname):
    x,y,w,h = box
    xmin,xmax,ymin,ymax = limits

    def f(u,v):
        return x+(u-xmin)/(xmax-xmin)*w, y+(v-ymin)/(ymax-ymin)*h

    for v, tag in yticks:
        _, yy = f(xmin, v)
        path(c, [(x,yy),(x+w,yy)], LINE if v else MUTED, .65)
        label(c, x-7, yy-3, tag, 10, MUTED, anchor="right")
    for u, tag in xticks:
        xx, _ = f(u, ymin)
        path(c, [(xx,y-4),(xx,y)], MUTED, .8)
        label(c, xx, y-16, tag, 10, MUTED, anchor="center")
    path(c, [(x,y+h),(x,y),(x+w,y)], MUTED, .8)
    label(c, x+w/2, y-35, xname, 11, INK, anchor="center")
    label(c, x, y+h+9, yname, 11, INK, bold=True)
    return f


def load(name):
    return json.loads((DATA / (name+".json")).read_text(encoding="utf-8-sig"))


def midpoint(x):
    return float(re.match(r"^\s*\[?\s*([-+0-9.eE]+)", x).group(1))


def complex_midpoint(value):
    return complex(midpoint(value["real"]), midpoint(value["imag"]))


def draw_proof():
    c = canvas("proof-chain", "One obstruction decides the whole family",
               "Schwarzschild  |  equal parent frequency  |  maximal daughter angular label", 272)
    statements = [
        ("Reconstruct the source", ["Quadratic Einstein tensor", "projected onto the", "daughter channel"]),
        ("Bound the rational poles", ["Every candidate fits", "in a 30-coefficient", "Laurent span"]),
        ("Check one witness", ["41 equations, 30 unknowns.", "The witness kills every", "column but sees the source"]),
        ("Factor the parity term", ["The witness is multiplied", "by (b - a)(b - rho a).", "Exactly two directions"]),
    ]
    for index, (heading, body) in enumerate(statements):
        x = 22+172*index
        rect(c,x,90,160,104,PALE)
        label(c,x+10,175,heading,12,INK,True)
        lines(c,x+10,154,body,11.5,16,MUTED)
        if index != 3:
            arrow(c,(x+161,143),(x+171,143))
    rect(c,22,23,676,48,"#E3F1EC")
    lines(c,34,51,["Lean checks the algebraic and radial steps. A conserved flux rules out a second",
                   "retarded field once the source and both radiation conditions are fixed."],12,15,TEAL)
    c.save()


def draw_polarization():
    rec = load("polarization-zeros-fine")
    E, X, O = map(complex_midpoint, rec["coefficients"].values())
    roots = list(map(complex_midpoint, rec["ratios_in_reference_parent_basis"]))
    rational = list(map(complex_midpoint, rec["rational_ratios"]))
    assert all(abs(E+X*r+O*r*r) < 1e-14 for r in roots)
    slope = abs(X)**2-2*abs(O)*(abs(E)+abs(O))
    assert slope > .0174 and abs(E)>abs(O)>0
    bars = [math.sqrt(2)*abs(O)] + [abs(-2*X*r)/(1+abs(r)**2) for r in roots]
    c = canvas("polarization", "Two ways to cancel one outgoing spin component",
               "Parent multipole 4, M times parent frequency = 1/2; daughter multipole 8", 345)
    f = axes(c,(64,77,322,171),(.92,1.42,-.099,.068),
             [(x,f"{x:.1f}") for x in (1.,1.1,1.2,1.3,1.4)],
             [(y,f"{y:.2f}") for y in (-.08,-.04,0,.04)],"Real part of b/a","Imaginary part")
    for idx, r in enumerate(rational,1):
        x,y = f(r.real,r.imag)
        dot(c,x,y,BLUE,5,True)
        label(c,x-3,y+10,f"R{idx}",11,BLUE,True)
    for idx, r in enumerate(roots,1):
        x,y = f(r.real,r.imag)
        dot(c,x,y,RUST,5)
        label(c,x+9,y-4,f"Z{idx}",11,RUST,True)
    label(c,64,31,"R  rational local field",11, BLUE, True)
    label(c,218,31,"Z  spin-minus zero",11,RUST,True)
    label(c,423,244,"Both outgoing spins",13,INK,True)
    label(c,423,226,"Norm per unit incident parity norm",10.5,MUTED)
    for i,(tag,value) in enumerate(zip(("Pure odd minimum","At Z1","At Z2"),bars,strict=True)):
        y=177-i*48
        label(c,423,y+17,tag,11.5, INK, True)
        rect(c,423,y,217*value/.37,10,"#156B55" if i==0 else "#A24923")
        label(c,430+217*value/.37,y-1,f"{value:.5f}",11,MUTED)
    c.save()


def draw_light_ring():
    J = load("light-ring-interference-20261125")
    dstar = J["equal_magnitude_detuning"]
    C = J["branch_two_scale"]
    F = lambda b: 1/(1+np.exp(np.pi*(2*b-1)))
    d = np.linspace(-.18,.78,300)
    fins = F(d/2)
    fds = np.sqrt(F(d))
    assert abs(float(F(dstar/2)-np.sqrt(F(dstar)))) < 1e-13
    c = canvas("light-ring", "Near the light ring, the second response has an envelope",
               "Fixed daughter detuning as angular momentum grows. The phase keeps changing.", 346)
    f = axes(c,(73,72,355,178),(-.18,.78,0,.016),
             [(v,f"{v:.2f}") for v in (0,.25,.5,.75)],[(v,f"{v:.3f}") for v in (0,.004,.008,.012,.016)],
             "Daughter detuning delta","Scaled strain magnitude")
    hi = [f(t,C*(a+b)) for t,a,b in zip(d,fins,fds,strict=True)]
    lo = [f(t,C*abs(a-b)) for t,a,b in zip(d,fins,fds,strict=True)]
    c.setFillColor(color("#E1F0EB"))
    p = c.beginPath()
    p.moveTo(*hi[0])
    for x,y in hi[1:]+lo[::-1]:
        p.lineTo(x,y)
    p.close()
    c.drawPath(p,fill=1,stroke=0)
    path(c,hi,TEAL,2.1)
    path(c,lo,RUST,2.0)
    xx,y0=f(dstar,0)
    path(c,[(xx,y0),(xx,f(dstar,.013)[1])],RUST,.8,[3,3])
    dot(c,xx,y0,RUST,3.5)
    label(c,xx+5,y0+9,"0.2347",10.5,RUST,True)
    label(c,452,247,"Why there are two curves",13,INK,True)
    lines(c,452,223,["The upper and lower curves", "are the largest and smallest", "subsequential limits."],11,15,MUTED)
    lines(c,452,162,["The relative phase advances", "by about half the logarithm", "of the parent angular label."],11,15,MUTED)
    lines(c,452,98,["At delta = 0.2347 the limiting", "magnitudes match. The lower", "limit reaches zero there."],11,15,RUST,True)
    c.save()


def draw_soft():
    rows = load("complex-strain-low-frequency-verified")
    differences = [midpoint(rows[k]["doubling_ratio"])-4 for k in ("4","5")]
    assert differences[0]<0<differences[1]
    c = canvas("soft-sign", "The first correction changes sign at multipole five",
               "Two outward-rounded low-frequency witnesses for the second exact mixture", 279)
    x0=363
    scale=252/.001
    path(c,[(x0,85),(x0,192)],MUTED,1.0)
    for i,(diff,lab) in enumerate(zip(differences,("Parent multipole 4","Parent multipole 5"),strict=True)):
        y=163-53*i
        x=x0+scale*diff
        col=BLUE if diff<0 else RUST
        rect(c,min(x0,x),y,abs(x-x0),15,col)
        label(c,94,y+20,lab,12,INK,True)
        label(c,x-9 if diff<0 else x+9,y+5,f"{4+diff:.8f}x",11.5,col,True,anchor="right" if diff<0 else "left")
    label(c,x0,66,"Exactly 4x",11,MUTED,anchor="center")
    label(c,22,23,"Doubling M times parent frequency from 1/2048 to 1/1024. A pure frequency-squared law gives 4x.",
          11,MUTED)
    c.save()


def draw_cover():
    c = Canvas(str(OUT / "x-cover.pdf"), pagesize=(1000,400), pageCompression=1)
    c.setTitle("A black-hole theorem, checked in Lean")
    rect(c,0,0,1000,400,"#10282F")
    for i in range(98,29,-1):
        c.setFillColor(Color(.08+.105*(i/98), .18+.20*(i/98), .19+.18*(i/98)))
        c.ellipse(740-i*2.05,187-i*.76,740+i*2.05,187+i*.76,stroke=0,fill=1)
    for i in range(10):
        cx=740
        rr=148+7*i
        xx=np.linspace(-.18,3.75,130)
        path(c,[(cx+rr*math.cos(t),188+rr*.41*math.sin(t)) for t in xx],
             "#415E57" if i%2 else "#68836C",.8)
    c.setFillColor(color("#06181E"))
    c.circle(740,189,66,stroke=0,fill=1)
    for s,t in [(35,23),(52,38),(65,55)]:
        path(c,[(741+s*math.cos(x),185+t*math.sin(x)) for x in np.linspace(.2,3.95,85)],"#637D6F",.7)
    label(c,46,335,"APTIFOLD RESEARCH",17,"#99D4B5",True)
    lines(c,46,270,["A black-hole theorem", "checked in Lean"],45,55,"#F1F5E4",True)
    lines(c,49,131,["Exactly two rational parity mixtures in", "quadratic Schwarzschild scattering"],
          18,24,"#C5DAD2")
    label(c,49,43,"CLASSICAL GENERAL RELATIVITY  /  FORMAL VERIFICATION",12,"#99D4B5",True)
    c.save()


if __name__ == "__main__":
    OUT.mkdir(exist_ok=True)
    for draw in (draw_proof,draw_polarization,draw_light_ring,draw_soft,draw_cover):
        draw()
