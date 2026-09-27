FROM python:3.11-slim

RUN apt-get update && apt-get install -y curl && \
    curl -L https://github.com/luau-lang/luau/releases/download/0.636/luau-linux -o /usr/local/bin/luau && \
    chmod +x /usr/local/bin/luau

WORKDIR /app
COPY requirements.txt .
RUN pip install -r requirements.txt
COPY bot.py .

CMD ["python", "bot.py"]
