FROM python:3.11-slim

# download luau binary
RUN apt-get update && apt-get install -y curl unzip && \
    curl -L https://github.com/luau-lang/luau/releases/download/0.636/luau-linux.zip -o luau.zip && \
    unzip luau.zip && \
    mv luau /usr/local/bin/luau && \
    chmod +x /usr/local/bin/luau && \
    rm luau.zip

WORKDIR /app
COPY requirements.txt .
RUN pip install -r requirements.txt
COPY bot.py .

CMD ["python", "bot.py"]
